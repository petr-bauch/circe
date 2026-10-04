/-
Circe.Emit.Fragment — admitted-fragment kind + shared small lemmas.

`FragKind` enumerates the admitted shapes; `matchFrag` itself lives in
`Circe.Emit.Match` (it must see every canonical `Func`). The word and
`Result`-map lemmas here are shared by several fragment modules, so they
live at the root of the `Emit` subtree instead of being imported sideways.
-/
import Circe.Base
import Circe.CoreIR
import Circe.Eval

/-! ## Fragment shapes -/

/-- The admitted fragment: `add`/`incr`/`choose`/`sum`/`vec`, extended in
    S1 with DAG calls (`addCall` = double-`add`, `sumCall` = `sum_array`
    delegation), in S2 with struct-by-value (`translate` = field-wise
    `Point` translation), in S3a with control flow (`nested` =
    nested bounded loops, `skip` = break/continue loop, `findEq` =
    early-return search, `cls` = switch-as-if-chain), and in S3b with
    64-bit loop-free widths (`add64` = signed-`nsw` `i64` add,
    `addu64` = wrapping `u64` add), in M1b with a `u64` heap block
    (`vec64` = `vec_alloc` at width 64), and in M1c with a grown `u32`
    heap block (`vecRealloc` = fill / `realloc` to `2*n` / fill-extension
    / sum), in M2a with POD const-methods (`methodSum` = the
    `_ZNK5Point3sumEv` leaf, `pointSumRef` = the single-call entry), in
    M2b with value ctors + trivial dtors (`accCtor` = the `_ZN3AccC2Ev`
    field-init leaf, `accAdd` = the `_ZN3Acc3addEi` checked-add leaf,
    `accGet` = the `_ZNK3Acc3getEv` identity leaf, `accDtor` = the
    `_ZN3AccD2Ev` no-op leaf, `accTwo` = the `cleanup`-scoped entry),
    in N4b with move semantics (`accMoveCtor` = the `_ZN3AccC2EOS_`
    move-ctor leaf, `moveAcc` = the nested-`cleanup` entry with the
    source-zeroing `assign`, `scopeEarly` = the early-return entry),
    and in N4a with overloads + namespaces (`add3` = the 3-`i32`
    overload leaf, `useAdd`/`useNsAdd` = single-delegation entries
    resolving to a mangled `add` leaf). -/
inductive FragKind : Type
  | add
  | add3
  | useAdd
  | useNsAdd
  | add64
  | addu64
  | incr
  | choose
  | sum
  | vec
  | vec64
  | vec2
  | vecRealloc
  | addCall
  | sumCall
  | translate
  | methodSum
  | pointSumRef
  | accCtor
  | accAdd
  | accGet
  | accDtor
  | accTwo
  | accMoveCtor
  | moveAcc
  | scopeEarly
  | boxThrough
  | nested
  | skip
  | findEq
  | cls
  deriving DecidableEq, Repr


/-! ### Small-number word lemmas (loop indices live below 2^32) -/

theorem ofNat32_zero : BitVec.ofNat 32 0 = 0 := rfl

theorem ofNat32_toNat (k : Nat) (h : k < 2 ^ 32) :
    (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- Incrementing a small word stays in `ofNat` form (no wrap).
    Stated with `ofNat 32 1` (not `1`): simp normalizes `1` to `1#32`. -/
theorem ofNat32_add_one (k : Nat) :
    BitVec.ofNat 32 k + BitVec.ofNat 32 1 = BitVec.ofNat 32 (k + 1) :=
  (BitVec.ofNat_add (n := 32) k 1).symm

/-- Unsigned comparison of a small word against any word. -/
theorem ofNat32_ult (k : Nat) (n : BitVec 32) (h : k < 2 ^ 32) :
    (BitVec.ofNat 32 k).ult n = decide (k < n.toNat) := by
  rw [BitVec.ult_eq_decide, ofNat32_toNat k h]

/-! ### Small-number 64-bit word lemmas (M1b: `u64` loop indices) -/

theorem ofNat64_zero : BitVec.ofNat 64 0 = 0 := rfl

theorem ofNat64_toNat (k : Nat) (h : k < 2 ^ 64) :
    (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- Incrementing a small 64-bit word stays in `ofNat` form (no wrap). -/
theorem ofNat64_add_one (k : Nat) :
    BitVec.ofNat 64 k + BitVec.ofNat 64 1 = BitVec.ofNat 64 (k + 1) :=
  (BitVec.ofNat_add (n := 64) k 1).symm

/-- Unsigned comparison of a small 64-bit word against any word. -/
theorem ofNat64_ult (k : Nat) (n : BitVec 64) (h : k < 2 ^ 64) :
    (BitVec.ofNat 64 k).ult n = decide (k < n.toNat) := by
  rw [BitVec.ult_eq_decide, ofNat64_toNat k h]

/-- `(<$>)` on `Result` computes on both constructors (for the corollaries).
    Proved by `rfl` (needs default transparency to see through the
    `Functor` instance, so later proofs use `exact`, not `simp`). -/
theorem i32_map_error (e : Panic) :
    Value.i32 <$> (Except.error e : Result (BitVec 32)) = .error e := rfl

theorem i32_map_ok (r : BitVec 32) :
    Value.i32 <$> (Except.ok r : Result (BitVec 32)) = .ok (.i32 r) := rfl

/-- `(<$>)` on `Result` computes on both constructors (for the 64-bit
    corollaries; cf. `i32_map_error`/`i32_map_ok`). -/
theorem i64_map_error (e : Panic) :
    Value.i64 <$> (Except.error e : Result (BitVec 64)) = .error e := rfl

theorem i64_map_ok (r : BitVec 64) :
    Value.i64 <$> (Except.ok r : Result (BitVec 64)) = .ok (.i64 r) := rfl

/-- `(<$>)` on `Result` computes on both constructors (for the corollaries;
    cf. `i32_map_error`/`i32_map_ok`). -/
theorem u32_map_error (e : Panic) :
    Value.u32 <$> (Except.error e : Result (BitVec 32)) = .error e := rfl

theorem u32_map_ok (r : BitVec 32) :
    Value.u32 <$> (Except.ok r : Result (BitVec 32)) = .ok (.u32 r) := rfl

/-- `(<$>)` on `Result` computes on both constructors (for the M1b `u64`
    corollaries; cf. `u32_map_error`/`u32_map_ok`). -/
theorem u64_map_error (e : Panic) :
    Value.u64 <$> (Except.error e : Result (BitVec 64)) = .error e := rfl

theorem u64_map_ok (r : BitVec 64) :
    Value.u64 <$> (Except.ok r : Result (BitVec 64)) = .ok (.u64 r) := rfl
