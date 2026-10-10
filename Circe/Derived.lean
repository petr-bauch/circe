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
import Circe.Emit.Array
import Circe.Emit.ArraySort
import Circe.Emit.Optional
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

/-! ## N4c: template-instantiation footprints (empty: owned scalars) -/

/-- `use_tadd32` entry footprints are trivially disjoint (same arg
    shape as the overload callers). -/
theorem oracleNoalias_useTadd32 (x y : BitVec 32) :
    oracleNoalias useTadd32Func [.i32 x, .i32 y] := by
  have hb : bindMemArgs useTadd32Func.args [.i32 x, .i32 y]
      emptyMem =
      some ([("x", .i32 x), ("y", .i32 y)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "x", ty := .i 32, role := .owned },
       { name := "y", ty := .i 32, role := .owned }]
      [.i32 x, .i32 y] emptyMem = _
    exact bindMemArgs_useAdd x y
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- 64-bit instantiation-caller binding pins nothing (two owned
    64-bit scalars). -/
theorem bindMemArgs_useTadd64 (x y : BitVec 64) :
    bindMemArgs
      [{ name := "x", ty := .i 64, role := .owned },
       { name := "y", ty := .i 64, role := .owned }]
      [.i64 x, .i64 y] emptyMem =
      some ([("x", .i64 x), ("y", .i64 y)], emptyMem, []) := by
  rfl

/-- `use_tadd64` entry footprints are trivially disjoint. -/
theorem oracleNoalias_useTadd64 (x y : BitVec 64) :
    oracleNoalias useTadd64Func [.i64 x, .i64 y] := by
  have hb : bindMemArgs useTadd64Func.args [.i64 x, .i64 y]
      emptyMem =
      some ([("x", .i64 x), ("y", .i64 y)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "x", ty := .i 64, role := .owned },
       { name := "y", ty := .i 64, role := .owned }]
      [.i64 x, .i64 y] emptyMem = _
    exact bindMemArgs_useTadd64 x y
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-! ## N4d-i `std::array` footprints: singleton block (reads only) -/

/-- `_S_ref` binding pins the 4-word array (single block) plus the
    owned index word. -/
theorem bindMemArgs_arrayRef (l : List (BitVec 32)) (n : BitVec 64) :
    bindMemArgs
      [{ name := "t", ty := .array (.i 32) 4, role := .sharedBorrow },
       { name := "n", ty := .u 64, role := .owned }]
      [.arr32 l, .u64 n] emptyMem =
      some ([("t", .arr32 l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("t", 0, 0)]) := by
  rfl

/-- `_S_ref` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_arrayRef (l : List (BitVec 32)) (n : BitVec 64) :
    oracleNoalias arrayRefFunc [.arr32 l, .u64 n] := by
  have hb : bindMemArgs arrayRefFunc.args [.arr32 l, .u64 n] emptyMem =
      some ([("t", .arr32 l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .array (.i 32) 4, role := .sharedBorrow },
       { name := "n", ty := .u 64, role := .owned }]
      [.arr32 l, .u64 n] emptyMem = _
    exact bindMemArgs_arrayRef l n
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `operator[]` binding pins the 4-word array (single block) plus the
    owned index word. -/
theorem bindMemArgs_arrayAt (l : List (BitVec 32)) (n : BitVec 64) :
    bindMemArgs
      [{ name := "a", ty := .array (.i 32) 4, role := .sharedBorrow },
       { name := "n", ty := .u 64, role := .owned }]
      [.arr32 l, .u64 n] emptyMem =
      some ([("a", .arr32 l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
  rfl

/-- `operator[]` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_arrayAt (l : List (BitVec 32)) (n : BitVec 64) :
    oracleNoalias arrayAtFunc [.arr32 l, .u64 n] := by
  have hb : bindMemArgs arrayAtFunc.args [.arr32 l, .u64 n] emptyMem =
      some ([("a", .arr32 l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
    show bindMemArgs
      [{ name := "a", ty := .array (.i 32) 4, role := .sharedBorrow },
       { name := "n", ty := .u 64, role := .owned }]
      [.arr32 l, .u64 n] emptyMem = _
    exact bindMemArgs_arrayAt l n
  have hn : LayoutNoAlias [("a", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `array_sum` binding pins the 4-word array (single block; the
    `callRet` delegations happen after entry). -/
theorem bindMemArgs_arraySum (a b c d : BitVec 32) :
    bindMemArgs
      [{ name := "a", ty := .array (.i 32) 4, role := .sharedBorrow }]
      [.arr32 [a, b, c, d]] emptyMem =
      some ([("a", .arr32 [a, b, c, d])],
        ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩, [("a", 0, 0)]) := by
  rfl

/-- `array_sum` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_arraySum (a b c d : BitVec 32) :
    oracleNoalias arraySumFunc [.arr32 [a, b, c, d]] := by
  have hb : bindMemArgs arraySumFunc.args [.arr32 [a, b, c, d]] emptyMem =
      some ([("a", .arr32 [a, b, c, d])],
        ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩, [("a", 0, 0)]) := by
    show bindMemArgs
      [{ name := "a", ty := .array (.i 32) 4, role := .sharedBorrow }]
      [.arr32 [a, b, c, d]] emptyMem = _
    exact bindMemArgs_arraySum a b c d
  have hn : LayoutNoAlias [("a", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N9 `insertion_sort` footprints: single block, mutated in place -/

/-- `insertion_sort` binding pins the `N`-word array (single block;
    `bindMemArgs` allocates by value shape, so the `mutBorrow` role
    binds exactly like the `sharedBorrow` reads). -/
theorem bindMemArgs_insertionSort (N : Nat) (l : List (BitVec 32)) :
    bindMemArgs
      [{ name := "a", ty := .array (.u 32) N, role := .mutBorrow 0 }]
      [.arr32 l] emptyMem =
      some ([("a", .arr32 l)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
  rfl

/-- `insertion_sort` footprints are a singleton (trivially disjoint;
    a single `&mut` array is containment — no second reference can
    collide). -/
theorem oracleNoalias_insertionSort (N : Nat) (l : List (BitVec 32)) :
    oracleNoalias (insertionSortFunc N) [.arr32 l] := by
  have hb : bindMemArgs (insertionSortFunc N).args [.arr32 l] emptyMem =
      some ([("a", .arr32 l)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
    show bindMemArgs
      [{ name := "a", ty := .array (.u 32) N, role := .mutBorrow 0 }]
      [.arr32 l] emptyMem = _
    exact bindMemArgs_insertionSort N l
  have hn : LayoutNoAlias [("a", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `array_sort_sum` entry binding pins nothing (no arguments; the
    array is a literal inside the body). -/
theorem bindMemArgs_arraySortSum :
    bindMemArgs arraySortSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) := by
  rfl

/-- `array_sort_sum` entry footprints are empty (trivially disjoint). -/
theorem oracleNoalias_arraySortSum :
    oracleNoalias arraySortSumEntryFunc [] := by
  have hb : bindMemArgs arraySortSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) :=
    bindMemArgs_arraySortSum
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-! ## N4d-ii `std::optional` footprints: 2-word block (reads only) -/

/-- Optional binding pins the 2-word `[payload, engaged]` block (the
    engaged-as-`1`/`0` encoding is the bind-time modeling choice:
    the payload word of a disengaged optional is unobservable when
    guarded, so it binds `0`). -/
theorem bindMemArgs_optVal (nm : String) (v : Option (BitVec 32)) :
    bindMemArgs
      [{ name := nm, ty := optObjTy, role := .sharedBorrow }]
      [.optVal v] emptyMem =
      some ([(nm, .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [(nm, 0, 0)]) := by
  rfl

/-- `_M_is_engaged` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_optHas (v : Option (BitVec 32)) :
    oracleNoalias optHasFunc [.optVal v] := by
  have hb : bindMemArgs optHasFunc.args [.optVal v] emptyMem =
      some ([("b", .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [("b", 0, 0)]) := by
    show bindMemArgs
      [{ name := "b", ty := optObjTy, role := .sharedBorrow }]
      [.optVal v] emptyMem = _
    exact bindMemArgs_optVal "b" v
  have hn : LayoutNoAlias [("b", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `has_value` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_optHasValue (v : Option (BitVec 32)) :
    oracleNoalias optHasValueFunc [.optVal v] := by
  have hb : bindMemArgs optHasValueFunc.args [.optVal v] emptyMem =
      some ([("o", .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [("o", 0, 0)]) := by
    show bindMemArgs
      [{ name := "o", ty := optObjTy, role := .sharedBorrow }]
      [.optVal v] emptyMem = _
    exact bindMemArgs_optVal "o" v
  have hn : LayoutNoAlias [("o", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Payload `_M_get` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_optGet (v : Option (BitVec 32)) :
    oracleNoalias optGetFunc [.optVal v] := by
  have hb : bindMemArgs optGetFunc.args [.optVal v] emptyMem =
      some ([("p", .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [("p", 0, 0)]) := by
    show bindMemArgs
      [{ name := "p", ty := optObjTy, role := .sharedBorrow }]
      [.optVal v] emptyMem = _
    exact bindMemArgs_optVal "p" v
  have hn : LayoutNoAlias [("p", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Impl `_M_get` footprints are a singleton (the `callRet`
    delegation happens after entry). -/
theorem oracleNoalias_optImplGet (v : Option (BitVec 32)) :
    oracleNoalias optImplGetFunc [.optVal v] := by
  have hb : bindMemArgs optImplGetFunc.args [.optVal v] emptyMem =
      some ([("o", .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [("o", 0, 0)]) := by
    show bindMemArgs
      [{ name := "o", ty := optObjTy, role := .sharedBorrow }]
      [.optVal v] emptyMem = _
    exact bindMemArgs_optVal "o" v
  have hn : LayoutNoAlias [("o", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `operator*` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_optDerefOp (v : Option (BitVec 32)) :
    oracleNoalias optDerefOpFunc [.optVal v] := by
  have hb : bindMemArgs optDerefOpFunc.args [.optVal v] emptyMem =
      some ([("o", .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [("o", 0, 0)]) := by
    show bindMemArgs
      [{ name := "o", ty := optObjTy, role := .sharedBorrow }]
      [.optVal v] emptyMem = _
    exact bindMemArgs_optVal "o" v
  have hn : LayoutNoAlias [("o", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `opt_deref` footprints are a singleton (the `callRet` delegations
    happen after entry). -/
theorem oracleNoalias_optDeref (v : Option (BitVec 32)) :
    oracleNoalias optDerefFunc [.optVal v] := by
  have hb : bindMemArgs optDerefFunc.args [.optVal v] emptyMem =
      some ([("o", .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [("o", 0, 0)]) := by
    show bindMemArgs
      [{ name := "o", ty := optObjTy, role := .sharedBorrow }]
      [.optVal v] emptyMem = _
    exact bindMemArgs_optVal "o" v
  have hn : LayoutNoAlias [("o", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N4d-iii `std::span` footprints: extent word + reified view (reads only) -/

/-- Span binding pins the `(1 + length)`-word
    `[(BitVec.ofNat 32 length)] ++ l` block (the `{ptr, extent}`
    object model: word `0` is the 32-bit extent, words `1+i` are
    the reified viewed elements). Stated over a general object
    type: `bindMemArgs` dispatches on the value alone, and the two
    span receivers (`spanObjTy`, `spanExtentObjTy`) share the
    `spanVal` value story. -/
theorem bindMemArgs_spanVal (nm : String) (ty : CType)
    (l : List (BitVec 32)) :
    bindMemArgs
      [{ name := nm, ty := ty, role := .sharedBorrow }]
      [.spanVal l] emptyMem =
      some ([(nm, .spanVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [(nm, 0, 0)]) := by
  rfl

/-- `_M_extent` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_spanExtent (l : List (BitVec 32)) :
    oracleNoalias spanExtentFunc [.spanVal l] := by
  have hb : bindMemArgs spanExtentFunc.args [.spanVal l] emptyMem =
      some ([("e", .spanVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("e", 0, 0)]) := by
    show bindMemArgs
      [{ name := "e", ty := spanExtentObjTy, role := .sharedBorrow }]
      [.spanVal l] emptyMem = _
    exact bindMemArgs_spanVal "e" spanExtentObjTy l
  have hn : LayoutNoAlias [("e", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `size` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_spanSize (l : List (BitVec 32)) :
    oracleNoalias spanSizeFunc [.spanVal l] := by
  have hb : bindMemArgs spanSizeFunc.args [.spanVal l] emptyMem =
      some ([("s", .spanVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := spanObjTy, role := .sharedBorrow }]
      [.spanVal l] emptyMem = _
    exact bindMemArgs_spanVal "s" spanObjTy l
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `operator[]` binding pins the `(1 + length)`-word block plus
    the owned index word (cf. `bindMemArgs_arrayAt`). -/
theorem bindMemArgs_spanIndex (l : List (BitVec 32)) (n : BitVec 64) :
    bindMemArgs
      [{ name := "s", ty := spanObjTy, role := .sharedBorrow },
       { name := "n", ty := .u 64, role := .owned }]
      [.spanVal l, .u64 n] emptyMem =
      some ([("s", .spanVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) := by
  rfl

/-- `operator[]` footprints are a singleton (the index is owned;
    the view is read-only). -/
theorem oracleNoalias_spanIndex (l : List (BitVec 32)) (n : BitVec 64) :
    oracleNoalias spanIndexFunc [.spanVal l, .u64 n] := by
  have hb : bindMemArgs spanIndexFunc.args [.spanVal l, .u64 n] emptyMem =
      some ([("s", .spanVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := spanObjTy, role := .sharedBorrow },
       { name := "n", ty := .u 64, role := .owned }]
      [.spanVal l, .u64 n] emptyMem = _
    exact bindMemArgs_spanIndex l n
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `span_sum` footprints are a singleton (the loop runs after
    entry over the read-only view). -/
theorem oracleNoalias_spanSum (l : List (BitVec 32)) :
    oracleNoalias spanSumFunc [.spanVal l] := by
  have hb : bindMemArgs spanSumFunc.args [.spanVal l] emptyMem =
      some ([("s", .spanVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := spanObjTy, role := .sharedBorrow }]
      [.spanVal l] emptyMem = _
    exact bindMemArgs_spanVal "s" spanObjTy l
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- View binding pins the `(1 + length)`-word
    `[(BitVec.ofNat 32 length)] ++ zero-extended-bytes` block (one
    byte per word cell, the word-level abstraction; N7a). -/
theorem bindMemArgs_viewVal (nm : String) (ty : CType)
    (l : List (BitVec 8)) :
    bindMemArgs
      [{ name := nm, ty := ty, role := .sharedBorrow }]
      [.viewVal l] emptyMem =
      some ([(nm, .viewVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩,
        [(nm, 0, 0)]) := by
  rfl

/-- `begin` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_viewBegin (l : List (BitVec 8)) :
    oracleNoalias viewBeginFunc [.viewVal l] := by
  have hb : bindMemArgs viewBeginFunc.args [.viewVal l] emptyMem =
      some ([("s", .viewVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := viewObjTy, role := .sharedBorrow }]
      [.viewVal l] emptyMem = _
    exact bindMemArgs_viewVal "s" viewObjTy l
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `end` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_viewEnd (l : List (BitVec 8)) :
    oracleNoalias viewEndFunc [.viewVal l] := by
  have hb : bindMemArgs viewEndFunc.args [.viewVal l] emptyMem =
      some ([("s", .viewVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := viewObjTy, role := .sharedBorrow }]
      [.viewVal l] emptyMem = _
    exact bindMemArgs_viewVal "s" viewObjTy l
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `view_sum` footprints are a singleton (the loop runs after
    entry over the read-only view). -/
theorem oracleNoalias_viewSum (l : List (BitVec 8)) :
    oracleNoalias viewSumFunc [.viewVal l] := by
  have hb : bindMemArgs viewSumFunc.args [.viewVal l] emptyMem =
      some ([("s", .viewVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := viewObjTy, role := .sharedBorrow }]
      [.viewVal l] emptyMem = _
    exact bindMemArgs_viewVal "s" viewObjTy l
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Vector binding pins the `(1 + length)`-word
    `[(BitVec.ofNat 32 length)] ++ l` block (the heap-triple
    snapshot model: word `0` is the length, words `1+i` are the
    reified elements; reads only, N4d-iv-a). Stated over a general
    object type: `bindMemArgs` dispatches on the value alone, and
    both vector receivers share the `stdVecVal` value story. -/
theorem bindMemArgs_stdVecVal (nm : String) (ty : CType)
    (l : List (BitVec 32)) :
    bindMemArgs
      [{ name := nm, ty := ty, role := .sharedBorrow }]
      [.stdVecVal l] emptyMem =
      some ([(nm, .stdVecVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [(nm, 0, 0)]) := by
  rfl

/-- `size` footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_stdVecSize (l : List (BitVec 32)) :
    oracleNoalias stdVecSizeFunc [.stdVecVal l] := by
  have hb : bindMemArgs stdVecSizeFunc.args [.stdVecVal l] emptyMem =
      some ([("s", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }]
      [.stdVecVal l] emptyMem = _
    exact bindMemArgs_stdVecVal "s" stdVecObjTy l
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `operator[]` binding pins the `(1 + length)`-word block plus
    the owned index word (cf. `bindMemArgs_spanIndex`). -/
theorem bindMemArgs_stdVecIndex (l : List (BitVec 32)) (n : BitVec 64) :
    bindMemArgs
      [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecVal l, .u64 n] emptyMem =
      some ([("s", .stdVecVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) := by
  rfl

/-- `operator[]` footprints are a singleton (the index is owned;
    the view is read-only). -/
theorem oracleNoalias_stdVecIndex (l : List (BitVec 32)) (n : BitVec 64) :
    oracleNoalias stdVecIndexFunc [.stdVecVal l, .u64 n] := by
  have hb : bindMemArgs stdVecIndexFunc.args [.stdVecVal l, .u64 n] emptyMem =
      some ([("s", .stdVecVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecVal l, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecIndex l n
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `vec_read_sum` footprints are a singleton (the loop runs after
    entry over the read-only view). -/
theorem oracleNoalias_stdVecReadSum (l : List (BitVec 32)) :
    oracleNoalias stdVecReadSumFunc [.stdVecVal l] := by
  have hb : bindMemArgs stdVecReadSumFunc.args [.stdVecVal l] emptyMem =
      some ([("s", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) := by
    show bindMemArgs
      [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }]
      [.stdVecVal l] emptyMem = _
    exact bindMemArgs_stdVecVal "s" stdVecObjTy l
  have hn : LayoutNoAlias [("s", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

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

/-- `cls_fall` binding pins nothing (one owned scalar; the fallthrough
    switch is an if-chain over pure comparisons). -/
theorem bindMemArgs_clsFall (x : BitVec 32) :
    bindMemArgs [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := by
  rfl

/-- `cls_fall` entry footprints are trivially disjoint. -/
theorem oracleNoalias_clsFall (x : BitVec 32) :
    oracleNoalias clsFallFunc [.u32 x] := by
  have hb : bindMemArgs clsFallFunc.args [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := by
    show bindMemArgs [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem = _
    exact bindMemArgs_clsFall x
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `cls_dense` binding pins nothing (one owned scalar; the dense
    switch is an if-chain over pure comparisons). -/
theorem bindMemArgs_clsDense (x : BitVec 32) :
    bindMemArgs [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := by
  rfl

/-- `cls_dense` entry footprints are trivially disjoint. -/
theorem oracleNoalias_clsDense (x : BitVec 32) :
    oracleNoalias clsDenseFunc [.u32 x] := by
  have hb : bindMemArgs clsDenseFunc.args [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := by
    show bindMemArgs [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem = _
    exact bindMemArgs_clsDense x
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `cls_break` binding pins nothing (one owned scalar; the local `r`
    never escapes — the epilogue returns its value). -/
theorem bindMemArgs_clsBreak (x : BitVec 32) :
    bindMemArgs [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := by
  rfl

/-- `cls_break` entry footprints are trivially disjoint. -/
theorem oracleNoalias_clsBreak (x : BitVec 32) :
    oracleNoalias clsBreakFunc [.u32 x] := by
  have hb : bindMemArgs clsBreakFunc.args [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := by
    show bindMemArgs [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem = _
    exact bindMemArgs_clsBreak x
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `cls_add` binding pins nothing (two owned scalars; the switch is an
    if-chain over pure comparisons and wrapping adds). -/
theorem bindMemArgs_clsAdd (x y : BitVec 32) :
    bindMemArgs [{ name := "x", ty := .u 32, role := .owned },
        { name := "y", ty := .u 32, role := .owned }]
      [.u32 x, .u32 y] emptyMem =
      some ([("x", .u32 x), ("y", .u32 y)], emptyMem, []) := by
  rfl

/-- `cls_add` entry footprints are trivially disjoint. -/
theorem oracleNoalias_clsAdd (x y : BitVec 32) :
    oracleNoalias clsAddFunc [.u32 x, .u32 y] := by
  have hb : bindMemArgs clsAddFunc.args [.u32 x, .u32 y] emptyMem =
      some ([("x", .u32 x), ("y", .u32 y)], emptyMem, []) := by
    show bindMemArgs [{ name := "x", ty := .u 32, role := .owned },
        { name := "y", ty := .u 32, role := .owned }]
      [.u32 x, .u32 y] emptyMem = _
    exact bindMemArgs_clsAdd x y
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

/-! ## N4d-iv-b1 growth leaves: owned-triple bindings -/

/-- Default-ctor binding pins nothing (no params). -/
theorem bindMemArgs_stdVecEmptyCtor :
    bindMemArgs stdVecEmptyCtorFunc.args [] emptyMem =
      some ([], emptyMem, []) := by
  rfl

/-- Default-ctor footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecEmptyCtor :
    oracleNoalias stdVecEmptyCtorFunc [] := by
  have hb : bindMemArgs stdVecEmptyCtorFunc.args [] emptyMem =
      some ([], emptyMem, []) := bindMemArgs_stdVecEmptyCtor
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- Empty-effect binding pins nothing (no params). -/
theorem bindMemArgs_stdVecUnit :
    bindMemArgs stdVecUnitFunc.args [] emptyMem =
      some ([], emptyMem, []) := by
  rfl

/-- Empty-effect footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecUnit :
    oracleNoalias stdVecUnitFunc [] := by
  have hb : bindMemArgs stdVecUnitFunc.args [] emptyMem =
      some ([], emptyMem, []) := bindMemArgs_stdVecUnit
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- Destructor binding pins the two-word header plus the storage
    words (the owned triple). -/
theorem bindMemArgs_stdVecDtor (b : Vec32) (len cap : Nat) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Destructor footprints are a singleton (trivially disjoint). -/
theorem oracleNoalias_stdVecDtor (b : Vec32) (len cap : Nat) :
    oracleNoalias stdVecDtorFunc [.stdVecOwned b len cap] := by
  have hb : bindMemArgs stdVecDtorFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecDtor b len cap
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Destroy-range binding pins nothing (two owned offsets). -/
theorem bindMemArgs_stdVecDestroyNoop (a b : BitVec 64) :
    bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
  rfl

/-- Destroy-range footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecDestroyNoop (a b : BitVec 64) :
    oracleNoalias stdVecDestroyNoopFunc [.u64 a, .u64 b] := by
  have hb : bindMemArgs stdVecDestroyNoopFunc.args [.u64 a, .u64 b]
      emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecDestroyNoop a b
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- Element-destroy binding pins nothing (one owned offset). -/
theorem bindMemArgs_stdVecDestroyPtr (p : BitVec 64) :
    bindMemArgs
      [{ name := "p", ty := .u 64, role := .owned }]
      [.u64 p] emptyMem =
      some ([("p", .u64 p)], emptyMem, []) := by
  rfl

/-- Element-destroy footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecDestroyPtr (p : BitVec 64) :
    oracleNoalias stdVecDestroyPtrFunc [.u64 p] := by
  have hb : bindMemArgs stdVecDestroyPtrFunc.args [.u64 p] emptyMem =
      some ([("p", .u64 p)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "p", ty := .u 64, role := .owned }]
      [.u64 p] emptyMem = _
    exact bindMemArgs_stdVecDestroyPtr p
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- Allocator-projection binding pins the owned triple (ignored by
    the body, like the value side). -/
theorem bindMemArgs_stdVecGetTp (b : Vec32) (len cap : Nat) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Allocator-projection footprints are a singleton. -/
theorem oracleNoalias_stdVecGetTp (b : Vec32) (len cap : Nat) :
    oracleNoalias stdVecGetTpFunc [.stdVecOwned b len cap] := by
  have hb : bindMemArgs stdVecGetTpFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecGetTp b len cap
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Max-size binding pins nothing (no params). -/
theorem bindMemArgs_stdVecDiffMax :
    bindMemArgs stdVecDiffMaxFunc.args [] emptyMem =
      some ([], emptyMem, []) := by
  rfl

/-- Max-size footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecDiffMax :
    oracleNoalias stdVecDiffMaxFunc [] := by
  have hb : bindMemArgs stdVecDiffMaxFunc.args [] emptyMem =
      some ([], emptyMem, []) := bindMemArgs_stdVecDiffMax
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `max` binding pins nothing (two owned words). -/
theorem bindMemArgs_stdVecMax (a b : BitVec 64) :
    bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
  rfl

/-- `max` footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecMax (a b : BitVec 64) :
    oracleNoalias stdVecMaxFunc [.u64 a, .u64 b] := by
  have hb : bindMemArgs stdVecMaxFunc.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecMax a b
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `min` binding pins nothing (two owned words). -/
theorem bindMemArgs_stdVecMin (a b : BitVec 64) :
    bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
  rfl

/-- `min` footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecMin (a b : BitVec 64) :
    oracleNoalias stdVecMinFunc [.u64 a, .u64 b] := by
  have hb : bindMemArgs stdVecMinFunc.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecMin a b
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `check_len` binding pins the triple plus the owned request word. -/
theorem bindMemArgs_stdVecCheckLen (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- `check_len` footprints are a singleton (the request is owned). -/
theorem oracleNoalias_stdVecCheckLen (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    oracleNoalias stdVecCheckLenFunc
      [.stdVecOwned b len cap, .u64 n] := by
  have hb : bindMemArgs stdVecCheckLenFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecCheckLen b len cap n
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `begin` binding pins the owned triple. -/
theorem bindMemArgs_stdVecBegin (b : Vec32) (len cap : Nat) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- `begin` footprints are a singleton. -/
theorem oracleNoalias_stdVecBegin (b : Vec32) (len cap : Nat) :
    oracleNoalias stdVecBeginFunc [.stdVecOwned b len cap] := by
  have hb : bindMemArgs stdVecBeginFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecBegin b len cap
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `end` binding pins the owned triple. -/
theorem bindMemArgs_stdVecEnd (b : Vec32) (len cap : Nat) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- `end` footprints are a singleton. -/
theorem oracleNoalias_stdVecEnd (b : Vec32) (len cap : Nat) :
    oracleNoalias stdVecEndFunc [.stdVecOwned b len cap] := by
  have hb : bindMemArgs stdVecEndFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecEnd b len cap
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `capacity` binding pins the owned triple (the `end` twin: same
    single-argument shape, so the same memory). -/
theorem bindMemArgs_stdVecGrowCapacity (b : Vec32) (len cap : Nat) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- `capacity` footprints are a singleton. -/
theorem oracleNoalias_stdVecGrowCapacity (b : Vec32) (len cap : Nat) :
    oracleNoalias stdVecGrowCapacityFunc [.stdVecOwned b len cap] := by
  have hb : bindMemArgs stdVecGrowCapacityFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecGrowCapacity b len cap
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `back` binding pins the owned triple. -/
theorem bindMemArgs_stdVecBack (b : Vec32) (len cap : Nat) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- `back` footprints are a singleton. -/
theorem oracleNoalias_stdVecBack (b : Vec32) (len cap : Nat) :
    oracleNoalias stdVecBackFunc [.stdVecOwned b len cap] := by
  have hb : bindMemArgs stdVecBackFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecBack b len cap
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Iterator-identity binding pins nothing (one owned offset). -/
theorem bindMemArgs_stdVecIterId (x : BitVec 64) :
    bindMemArgs
      [{ name := "p", ty := .u 64, role := .owned }]
      [.u64 x] emptyMem =
      some ([("p", .u64 x)], emptyMem, []) := by
  rfl

/-- Iterator-identity footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecIterId (x : BitVec 64) :
    oracleNoalias stdVecIterIdFunc [.u64 x] := by
  have hb : bindMemArgs stdVecIterIdFunc.args [.u64 x] emptyMem =
      some ([("p", .u64 x)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "p", ty := .u 64, role := .owned }]
      [.u64 x] emptyMem = _
    exact bindMemArgs_stdVecIterId x
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `miEl` binding pins nothing (two owned offsets). -/
theorem bindMemArgs_stdVecMinusEl (it n : BitVec 64) :
    bindMemArgs
      [{ name := "it", ty := .u 64, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.u64 it, .u64 n] emptyMem =
      some ([("it", .u64 it), ("n", .u64 n)], emptyMem, []) := by
  rfl

/-- `miEl` footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecMinusEl (it n : BitVec 64) :
    oracleNoalias stdVecMinusElFunc [.u64 it, .u64 n] := by
  have hb : bindMemArgs stdVecMinusElFunc.args [.u64 it, .u64 n] emptyMem =
      some ([("it", .u64 it), ("n", .u64 n)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "it", ty := .u 64, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.u64 it, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecMinusEl it n
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `mi` binding pins nothing (two owned offsets). -/
theorem bindMemArgs_stdVecMinus (a b : BitVec 64) :
    bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
  rfl

/-- `mi` footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecMinus (a b : BitVec 64) :
    oracleNoalias stdVecMinusFunc [.u64 a, .u64 b] := by
  have hb : bindMemArgs stdVecMinusFunc.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecMinus a b
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- Allocate binding pins nothing (one owned request word). -/
theorem bindMemArgs_stdVecAlloc (n : BitVec 64) :
    bindMemArgs
      [{ name := "n", ty := .u 64, role := .owned }]
      [.u64 n] emptyMem =
      some ([("n", .u64 n)], emptyMem, []) := by
  rfl

/-- Allocate footprints are trivially disjoint (fresh storage pins
    after the call, not at entry). -/
theorem oracleNoalias_stdVecAlloc (n : BitVec 64) :
    oracleNoalias stdVecAllocFunc [.u64 n] := by
  have hb : bindMemArgs stdVecAllocFunc.args [.u64 n] emptyMem =
      some ([("n", .u64 n)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "n", ty := .u 64, role := .owned }]
      [.u64 n] emptyMem = _
    exact bindMemArgs_stdVecAlloc n
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- Deallocate binding pins the owned triple. -/
theorem bindMemArgs_stdVecDealloc (b : Vec32) (len cap : Nat) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Deallocate footprints are a singleton. -/
theorem oracleNoalias_stdVecDealloc (b : Vec32) (len cap : Nat) :
    oracleNoalias stdVecDeallocFunc [.stdVecOwned b len cap] := by
  have hb : bindMemArgs stdVecDeallocFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecDealloc b len cap
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Guarded-deallocate binding pins the triple plus the owned count. -/
theorem bindMemArgs_stdVecDeallocGuard (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Guarded-deallocate footprints are a singleton (the count is
    owned). -/
theorem oracleNoalias_stdVecDeallocGuard (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    oracleNoalias stdVecDeallocGuardFunc
      [.stdVecOwned b len cap, .u64 n] := by
  have hb : bindMemArgs stdVecDeallocGuardFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecDeallocGuard b len cap n
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Construct binding pins the triple plus the owned offset/word. -/
theorem bindMemArgs_stdVecConstruct (b : Vec32) (len cap : Nat)
    (p : BitVec 64) (x : BitVec 32) :
    bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "p", ty := .u 64, role := .owned },
       { name := "v", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 p, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Construct footprints are a singleton (offset and word are
    owned). -/
theorem oracleNoalias_stdVecConstruct (b : Vec32) (len cap : Nat)
    (p : BitVec 64) (x : BitVec 32) :
    oracleNoalias stdVecConstructFunc
      [.stdVecOwned b len cap, .u64 p, .i32 x] := by
  have hb : bindMemArgs stdVecConstructFunc.args
      [.stdVecOwned b len cap, .u64 p, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "p", ty := .u 64, role := .owned },
       { name := "v", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 p, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecConstruct b len cap p x
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Relocate binding pins both triples (unwind order: `dst` takes
    address `0`, `src` takes address `1`); the three offsets are
    owned. -/
theorem bindMemArgs_stdVecReloc (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat)
    (first last result : BitVec 64) :
    bindMemArgs
      [{ name := "src", ty := .vecBlock, role := .owned },
       { name := "dst", ty := .vecBlock, role := .owned },
       { name := "first", ty := .u 64, role := .owned },
       { name := "last", ty := .u 64, role := .owned },
       { name := "result", ty := .u 64, role := .owned }]
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] emptyMem =
      some ([("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)],
        ⟨2, [(1, ⟨1, !bS.freed, (BitVec.ofNat 32 lenS) ::
          (BitVec.ofNat 32 capS) :: bS.val⟩),
          (1, ⟨1, true, (BitVec.ofNat 32 lenS) ::
          (BitVec.ofNat 32 capS) :: bS.val⟩),
          (0, ⟨0, !bD.freed, (BitVec.ofNat 32 lenD) ::
          (BitVec.ofNat 32 capD) :: bD.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 lenD) ::
          (BitVec.ofNat 32 capD) :: bD.val⟩)], []⟩,
        [("src", 1, 1), ("dst", 0, 0)]) := by
  rfl

/-- Relocate footprints are two disjoint singletons (source and
    destination buffers never alias at entry). -/
theorem oracleNoalias_stdVecReloc (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat)
    (first last result : BitVec 64) :
    oracleNoalias stdVecRelocFunc
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] := by
  have hb : bindMemArgs stdVecRelocFunc.args
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] emptyMem =
      some ([("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)],
        ⟨2, [(1, ⟨1, !bS.freed, (BitVec.ofNat 32 lenS) ::
          (BitVec.ofNat 32 capS) :: bS.val⟩),
          (1, ⟨1, true, (BitVec.ofNat 32 lenS) ::
          (BitVec.ofNat 32 capS) :: bS.val⟩),
          (0, ⟨0, !bD.freed, (BitVec.ofNat 32 lenD) ::
          (BitVec.ofNat 32 capD) :: bD.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 lenD) ::
          (BitVec.ofNat 32 capD) :: bD.val⟩)], []⟩,
        [("src", 1, 1), ("dst", 0, 0)]) := by
    show bindMemArgs
      [{ name := "src", ty := .vecBlock, role := .owned },
       { name := "dst", ty := .vecBlock, role := .owned },
       { name := "first", ty := .u 64, role := .owned },
       { name := "last", ty := .u 64, role := .owned },
       { name := "result", ty := .u 64, role := .owned }]
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] emptyMem = _
    exact bindMemArgs_stdVecReloc bS lenS capS bD lenD capD
      first last result
  have hn : LayoutNoAlias [("src", 1, 1), ("dst", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N4d-iv-b2 `_M_realloc_insert` composer: entry binding + footprint -/

/-- Realloc binding pins the owned triple (the composer takes the old
    triple by value plus the position and element words). -/
theorem bindMemArgs_stdVecGrowRealloc (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) :
    bindMemArgs stdVecGrowReallocFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Realloc footprints are a singleton (the old triple is owned; the
    position and element words are pure). -/
theorem oracleNoalias_stdVecGrowRealloc (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) :
    oracleNoalias stdVecGrowReallocFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
  have hb : bindMemArgs stdVecGrowReallocFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecGrowRealloc b len cap pos x
  have hn : LayoutNoAlias [("t", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N4d-iv-b2 `emplace_back` composer: entry binding + footprint -/

/-- Emplace binding pins the owned triple (the composer takes the old
    triple by value plus the element word). -/
theorem bindMemArgs_stdVecEmplaceBack (b : Vec32) (len cap : Nat)
    (x : BitVec 32) :
    bindMemArgs stdVecEmplaceBackFunc.args
      [.stdVecOwned b len cap, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Emplace footprints are a singleton (the old triple is owned; the
    element word is pure). -/
theorem oracleNoalias_stdVecEmplaceBack (b : Vec32) (len cap : Nat)
    (x : BitVec 32) :
    oracleNoalias stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x] := by
  have hb : bindMemArgs stdVecEmplaceBackFunc.args
      [.stdVecOwned b len cap, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecEmplaceBack b len cap x
  have hn : LayoutNoAlias [("t", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N4d-iv-b2 `push_back` forwarder: entry binding + footprint -/

/-- Push-back binding pins the owned triple (same `(t, x)` params as
    `emplace_back`: the forwarder takes the old triple by value plus
    the element word). -/
theorem bindMemArgs_stdVecPushBack (b : Vec32) (len cap : Nat)
    (x : BitVec 32) :
    bindMemArgs stdVecPushBackFunc.args
      [.stdVecOwned b len cap, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Push-back footprints are a singleton (the old triple is owned; the
    element word is pure). -/
theorem oracleNoalias_stdVecPushBack (b : Vec32) (len cap : Nat)
    (x : BitVec 32) :
    oracleNoalias stdVecPushBackFunc
      [.stdVecOwned b len cap, .i32 x] := by
  have hb : bindMemArgs stdVecPushBackFunc.args
      [.stdVecOwned b len cap, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecPushBack b len cap x
  have hn : LayoutNoAlias [("t", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N7b `reserve` composer: entry binding + footprint -/

/-- Reserve binding pins the owned triple (same `(t, n)` params as the
    index leaf: the composer takes the old triple by value plus the
    requested capacity word). -/
theorem bindMemArgs_stdVecReserve (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    bindMemArgs stdVecReserveFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Reserve footprints are a singleton (the old triple is owned; the
    requested capacity word is pure). -/
theorem oracleNoalias_stdVecReserve (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    oracleNoalias stdVecReserveFunc
      [.stdVecOwned b len cap, .u64 n] := by
  have hb : bindMemArgs stdVecReserveFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecReserve b len cap n
  have hn : LayoutNoAlias [("t", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N4d-iv-b2 entry-scoped `operator[]` leaf: entry binding + footprint -/

/-- Index binding pins the owned triple (the leaf takes the triple by
    value plus the index word). -/
theorem bindMemArgs_stdVecGrowIndex (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    bindMemArgs stdVecGrowIndexFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Index footprints are a singleton (the old triple is owned; the
    index word is pure). -/
theorem oracleNoalias_stdVecGrowIndex (b : Vec32) (len cap : Nat)
    (n : BitVec 64) :
    oracleNoalias stdVecGrowIndexFunc
      [.stdVecOwned b len cap, .u64 n] := by
  have hb : bindMemArgs stdVecGrowIndexFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecGrowIndex b len cap n
  have hn : LayoutNoAlias [("t", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N4d-iv-b2 `vec_push_sum` entry: entry binding + footprint -/

/-- Entry binding: no arguments, empty footprint. -/
theorem bindMemArgs_vecPushSumEntry :
    bindMemArgs vecPushSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) := rfl

/-- Entry footprints are trivially disjoint (nothing pinned). -/
theorem oracleNoalias_vecPushSumEntry :
    oracleNoalias vecPushSumEntryFunc [] := by
  exact ⟨_, _, _, bindMemArgs_vecPushSumEntry, layoutNoAlias_nil⟩

/-! ## N7b `vec_reserve_sum` entry: entry binding + footprint -/

/-- Entry binding: no arguments, empty footprint. -/
theorem bindMemArgs_vecReserveSumEntry :
    bindMemArgs vecReserveSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) := rfl

/-- Entry footprints are trivially disjoint (nothing pinned). -/
theorem oracleNoalias_vecReserveSumEntry :
    oracleNoalias vecReserveSumEntryFunc [] := by
  exact ⟨_, _, _, bindMemArgs_vecReserveSumEntry, layoutNoAlias_nil⟩

/-! ## N7c iterator leaves: `plEl` / `iterEq` bindings + footprints -/

/-- `plEl` binding pins nothing (two owned offsets). -/
theorem bindMemArgs_stdVecPlusEl (it n : BitVec 64) :
    bindMemArgs
      [{ name := "it", ty := .u 64, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.u64 it, .u64 n] emptyMem =
      some ([("it", .u64 it), ("n", .u64 n)], emptyMem, []) := by
  rfl

/-- `plEl` footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecPlusEl (it n : BitVec 64) :
    oracleNoalias stdVecPlusElFunc [.u64 it, .u64 n] := by
  have hb : bindMemArgs stdVecPlusElFunc.args [.u64 it, .u64 n] emptyMem =
      some ([("it", .u64 it), ("n", .u64 n)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "it", ty := .u 64, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.u64 it, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecPlusEl it n
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `iterEq` binding pins nothing (two owned offsets). -/
theorem bindMemArgs_stdVecIterEq (a b : BitVec 64) :
    bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
  rfl

/-- `iterEq` footprints are trivially disjoint. -/
theorem oracleNoalias_stdVecIterEq (a b : BitVec 64) :
    oracleNoalias stdVecIterEqFunc [.u64 a, .u64 b] := by
  have hb : bindMemArgs stdVecIterEqFunc.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecIterEq a b
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-! ## N7c backward shift: entry binding + footprint -/

/-- Shift binding pins the owned triple (the words are pure offsets). -/
theorem bindMemArgs_stdVecShiftBack (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) :
    bindMemArgs stdVecShiftBackFunc.args
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result]
      emptyMem =
      some ([("t", .stdVecOwned b len cap), ("first", .u64 first),
        ("last", .u64 last), ("result", .u64 result)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Shift footprints are a singleton (the triple is owned; the words
    are pure). -/
theorem oracleNoalias_stdVecShiftBack (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) :
    oracleNoalias stdVecShiftBackFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last,
        .u64 result] := by
  have hb : bindMemArgs stdVecShiftBackFunc.args
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result]
      emptyMem =
      some ([("t", .stdVecOwned b len cap), ("first", .u64 first),
        ("last", .u64 last), ("result", .u64 result)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "first", ty := .u 64, role := .owned },
       { name := "last", ty := .u 64, role := .owned },
       { name := "result", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result]
      emptyMem = _
    exact bindMemArgs_stdVecShiftBack b len cap first last result
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N7c insert composers: entry bindings + footprints -/

/-- Aux binding pins the owned triple (position and word are pure). -/
theorem bindMemArgs_stdVecInsertAux (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) :
    bindMemArgs stdVecInsertAuxFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Aux footprints are a singleton. -/
theorem oracleNoalias_stdVecInsertAux (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) :
    oracleNoalias stdVecInsertAuxFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
  have hb : bindMemArgs stdVecInsertAuxFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecInsertAux b len cap pos x
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Rval binding pins the owned triple (position and word are pure). -/
theorem bindMemArgs_stdVecInsertRval (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) :
    bindMemArgs stdVecInsertRvalFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Rval footprints are a singleton. -/
theorem oracleNoalias_stdVecInsertRval (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) :
    oracleNoalias stdVecInsertRvalFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
  have hb : bindMemArgs stdVecInsertRvalFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecInsertRval b len cap pos x
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Forwarder binding pins the owned triple (position and word are pure). -/
theorem bindMemArgs_stdVecInsert (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) :
    bindMemArgs stdVecInsertFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Forwarder footprints are a singleton. -/
theorem oracleNoalias_stdVecInsert (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) :
    oracleNoalias stdVecInsertFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
  have hb : bindMemArgs stdVecInsertFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecInsert b len cap pos x
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N7c `vec_insert_sum` entry: entry binding + footprint -/

/-- Entry binding: no arguments, empty footprint. -/
theorem bindMemArgs_vecInsertSumEntry :
    bindMemArgs vecInsertSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) := rfl

/-- Entry footprints are trivially disjoint (nothing pinned). -/
theorem oracleNoalias_vecInsertSumEntry :
    oracleNoalias vecInsertSumEntryFunc [] := by
  exact ⟨_, _, _, bindMemArgs_vecInsertSumEntry, layoutNoAlias_nil⟩

/-! ## N7d forward shift: entry binding + footprint -/

/-- Shift-down binding pins the owned triple (the words are pure offsets). -/
theorem bindMemArgs_stdVecShiftDown (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) :
    bindMemArgs stdVecShiftDownFunc.args
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result]
      emptyMem =
      some ([("t", .stdVecOwned b len cap), ("first", .u64 first),
        ("last", .u64 last), ("result", .u64 result)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Shift-down footprints are a singleton (the triple is owned; the words
    are pure). -/
theorem oracleNoalias_stdVecShiftDown (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) :
    oracleNoalias stdVecShiftDownFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last,
        .u64 result] := by
  have hb : bindMemArgs stdVecShiftDownFunc.args
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result]
      emptyMem =
      some ([("t", .stdVecOwned b len cap), ("first", .u64 first),
        ("last", .u64 last), ("result", .u64 result)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "first", ty := .u 64, role := .owned },
       { name := "last", ty := .u 64, role := .owned },
       { name := "result", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result]
      emptyMem = _
    exact bindMemArgs_stdVecShiftDown b len cap first last result
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N7d erase composers: entry bindings + footprints -/

/-- Erase-core binding pins the owned triple (position is pure). -/
theorem bindMemArgs_stdVecEraseCore (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) :
    bindMemArgs stdVecEraseCoreFunc.args
      [.stdVecOwned b len cap, .u64 pos] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Erase-core footprints are a singleton. -/
theorem oracleNoalias_stdVecEraseCore (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) :
    oracleNoalias stdVecEraseCoreFunc
      [.stdVecOwned b len cap, .u64 pos] := by
  have hb : bindMemArgs stdVecEraseCoreFunc.args
      [.stdVecOwned b len cap, .u64 pos] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos] emptyMem = _
    exact bindMemArgs_stdVecEraseCore b len cap pos
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Erase-forwarder binding pins the owned triple (position is pure). -/
theorem bindMemArgs_stdVecErase (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) :
    bindMemArgs stdVecEraseFunc.args
      [.stdVecOwned b len cap, .u64 pos] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
  rfl

/-- Erase-forwarder footprints are a singleton. -/
theorem oracleNoalias_stdVecErase (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) :
    oracleNoalias stdVecEraseFunc
      [.stdVecOwned b len cap, .u64 pos] := by
  have hb : bindMemArgs stdVecEraseFunc.args
      [.stdVecOwned b len cap, .u64 pos] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos)],
        ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩,
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos] emptyMem = _
    exact bindMemArgs_stdVecErase b len cap pos
  have hn : LayoutNoAlias [("t", 0, 0)] := by simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## N7d `vec_erase_sum` entry: entry binding + footprint -/

/-- Entry binding: no arguments, empty footprint. -/
theorem bindMemArgs_vecEraseSumEntry :
    bindMemArgs vecEraseSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) := rfl

/-- Entry footprints are trivially disjoint (nothing pinned). -/
theorem oracleNoalias_vecEraseSumEntry :
    oracleNoalias vecEraseSumEntryFunc [] := by
  exact ⟨_, _, _, bindMemArgs_vecEraseSumEntry, layoutNoAlias_nil⟩

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
