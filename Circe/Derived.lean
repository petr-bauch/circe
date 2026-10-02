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
import Circe.Emit.Flow

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

/-! ## Single-array shapes: singleton footprint -/

/-- `sum_caller` binding pins exactly the array block (mirrors
    `bindMemArgs_sum`; the call itself happens after entry). -/
theorem bindMemArgs_sumCaller (l : List (BitVec 32)) (nv : BitVec 32) :
    bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)]) := by
  rfl

/-- `sum_caller` entry footprints are a singleton. -/
theorem oracleNoalias_sumCaller (l : List (BitVec 32)) (nv : BitVec 32) :
    oracleNoalias sumCallerFunc [.arr32 l, .u32 nv] := by
  have hb : bindMemArgs sumCallerFunc.args [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)]) := by
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
        ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)]) := by
  rfl

/-- `find_eq` entry footprints are a singleton. -/
theorem oracleNoalias_findEq (l : List (BitVec 32)) (nv kv : BitVec 32) :
    oracleNoalias findEqFunc [.arr32 l, .u32 nv, .u32 kv] := by
  have hb : bindMemArgs findEqFunc.args [.arr32 l, .u32 nv, .u32 kv]
      emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv), ("k", .u32 kv)],
        ⟨1, [(0, ⟨0, true, l⟩)]⟩, [("a", 0, 0)]) := by
    show bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned },
       { name := "k", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv, .u32 kv] emptyMem = _
    exact bindMemArgs_findEq l nv kv
  have hn : LayoutNoAlias [("a", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

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
