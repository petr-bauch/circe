# Ownership Discipline (normative for v0.1)

Follows Aeneas: translate values, not memory. Pointers are ownership roles,
not addresses. The Clang/CIR + LLVM-AA oracle certifies uniqueness;
`validate` rejects everything else.

## Roles

- **owned**: by-value locals/params/returns (ints, structs, arrays-as-lists).
- **mutBorrow(region)**: `T *__restrict` param, unique for its region.
  Caller `f(&y)` becomes `y ← f_fwd y` (value in, updated value out).
- **sharedBorrow**: `const T *` with length param; becomes a pure
  `List`/`Array` argument (copy semantics for verification).

## Rules

1. `T*` params must be `__restrict__` or oracle-proven `noalias`.
2. No two live params may alias (oracle verdict required).
3. No escaping: no storing a param pointer to a global, no returning
   interior pointers except the borrow-return pattern below.
4. Indexing only as `p[i]`/`*(p+i)` with `0 <= i < n`, `n` a same-function
   length argument.
5. `&x` may only feed a `restrict` call in the same scope (no escape).
6. Borrow-return (`choose`-shape): a `T*` return must be exactly one of the
   `T*` inputs. Generates forward + backward functions:
   ```c
   int32_t *choose(bool b, int32_t *__restrict x, int32_t *__restrict y);
   -- fwd:  choose_fwd b x y : Result BV32
   -- back: choose_back b x y ret : Result (BV32 × BV32)
   ```
   Single-region only in v0.1; nested/multiple regions are rejected.
7. Loops over arrays require the length-paired form (`sum_array`); general
   pointer-chasing loops are out. v0.1 loops must terminate within
   `EVAL_FUEL` (4096) iterations; exhaustion reports `AssertFail`
   (incompleteness, never unsoundness), and over-long lengths report `OOB`.

`validate` maps each admitted shape to its canonical `Func`
(`addFunc`/`incrFunc`/`chooseFunc`/`sumFunc` with the source name) — the
only `Func`s the emitter handles (`matchFrag` contract, `Circe.Emit`).

## Normative translation schema (PLAN.md §6)

Values, not addresses. Every example below is a pure equation over
`Circe.Base` (`Result`, `BitVec`); no memory model appears.

```c
void incr(int32_t *__restrict p) { *p = *p + 1; }
// → def incr_fwd (p : BitVec 32) : Result (BitVec 32) := checkedIncrI32 p
// caller `incr(&y)` → `y ← incr_fwd y`

uint32_t sum_array(const uint32_t *__restrict a, size_t n) { … a[i] … }
// → def sum_fwd (a : List (BitVec 32)) (n : Nat) (h : a.length = n)
//     : Result (BitVec 32) := …
// `a` is a `sharedBorrow`: a pure list argument (copy semantics).
```

Emitter correctness for every admitted op:

```lean
theorem emit_correct (f : Func) (ρ : Env) :
  evalLean (emitFunc f) ρ = Eval f ρ
```

## Oracle

Source: Clang lifetime analysis + CIR lifetime-checker prototype +
LLVM `basicaa` `noalias` verdicts, imported as per-function facts.
Conservative = reject. `__restrict__` noalias evidence is visible in the
checked-in goldens (`{llvm.noalias, llvm.noundef}` attrs); deeper
`-fsave-optimization-record` dumps land in Phase 4 (`tests/oracle/`
placeholder remains, see `docs/PINS.md`).
