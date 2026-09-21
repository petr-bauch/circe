# Circe — CIR → Lean4 Verification: Bootstrap Plan

## 1. Goal

Build a verification pipeline for C (MVP subset) that:

1. Takes C source → ClangIR (CIR, raw `CIRGen` output) via
   `clang -fclangir -emit-cir -fclangir-disable-passes`.
2. Translates CIR to pure, memory-free Lean4 via an **emitter written in
   Lean4**, with **machine-checked correctness proofs** (verified emitter).
3. Supports **functional correctness proofs** as pure equations, à la
   **Aeneas for Rust**: no memory model, no separation logic, no
   framing lemmas in the common case.

Non-goals for MVP: arbitrary C aliasing, full C++ (classes/templates/EH),
concurrency, float reasoning beyond stubs, verified C parser, full ABI
lowering.

## 2. Background / Constraints

- CIR source of truth is `llvm/llvm-project` main (label `ClangIR`).
  Incubator `llvm/clangir` archived Feb 2026. **Pin a `llvm-project` SHA.**
- CIR status: C mostly covered, C++ partial (missing cleanup/EH).
  ABI lowering (`-fclangir-call-conv-lowering`) WIP — MVP uses raw
  `CIRGen` output to avoid reasoning about CIR passes.
- Output is MLIR text (`cir.func`, `cir.alloca/load/store`, `cir.br`,
  `cir.cast`, `cir.binop/cmp`, `cir.get_member`, `cir.scope`, …).

## 3. Approach: Aeneas-Style Functional Translation for C

### 3.1 Aeneas in one paragraph

Aeneas (Ho & Protzenko, ICFP'22) translates Rust MIR/LLBC to a pure
lambda calculus. It works because Rust's borrow checker already guarantees
unique ownership: `&mut T` is a unique capability, `&T` is freely
shareable/copyable. Translation: values map to values (no addresses);
a call `f(&mut x)` becomes `x := f_fwd x`; a function returning a borrow
`fn choose(b,x:&mut,y:&mut)->&mut` becomes a **forward** function
(`call` flowing forward) plus a **backward** function (propagating the
updated return value back to `x,y` when the region ends). Shared borrows
become pure copies. Panics/overflow become a `Result` error monad.
Correctness is proved against an ownership-centric (loan-based) semantics,
not a flat heap. The proof engineer then reasons equationally in F*/Lean.

### 3.2 Why C is harder — and the MVP answer

C has no borrow checker: arbitrary aliasing, pointer arithmetic,
`void*`/int-ptr casts, globals, `malloc`/`free` with manual discipline.
A pure translation is only sound where **unique ownership can be
established**. MVP decision (locked):

- **Strict pure-only:** anything whose uniqueness cannot be established
  is **rejected loudly**. No memory-model fallback in v0.1. This is the
  closest faithful port of Aeneas and keeps proofs memory-free.
- **Ownership oracle:** uniqueness comes from **Clang/CIR analysis**
  (lifetime analysis + CIR lifetime-checker prototype + LLVM alias
  analysis `basicaa`), not from user proofs. The translator trusts the
  oracle's "no-alias" verdict per function; the validator rejects the
  function if the oracle is inconclusive.

Explicit soundness gap (documented, not hidden): oracle + `CIRGen` are
trusted in v0.1. Later work: formalize the ownership semantics against
Stacked Borrows / CompCert-style memory and shrink the trust base.

### 3.3 Pipeline

```
C source (+ restrict discipline, §4)
  → clang -fclangir … → foo.cir (MLIR text)
  → [unverified, trusted] Parser (Lean exe): text → RawIR
  → [oracle query] Clang/CIR lifetime + LLVM AA verdicts → attach to RawIR
  → [verified] validate : RawIR → Option CoreIR  (rejects aliasing/out-of-subset)
  → [verified] Emit : CoreIR → Lean (forward + backward defs)
  → out/Foo.lean importing Circe.Base, checked by `lake build`
```

Trust boundary: Clang/CIRGen, CIR syntax, oracle verdicts, Lean+Mathlib
are trusted. `CoreIR`, ownership semantics `Eval`, `Emit`, and
`emit_correct` are verified in Lean. `validate` is the gate: unverified
text can never reach `Emit` without passing it.

## 4. Ownable-C Subset MVP (Frozen for v0.1)

Design rule: if it cannot be functionalized, it is out.

Types: `void`, `_Bool`, `i8/i16/i32/i64`, `u8/u16/u32/u64`,
`T*` (only as unique-borrow parameters/returns or array-with-length),
arrays (only via length-paired params), structs (no bitfields/unions/
variadics in v0.1). No `void*`, no int↔ptr casts, no `volatile`,
no `_Atomic`, no function pointers in v0.1.

Statements: functions, locals, `if/while/for`, `return`, `break/continue`,
arithmetic/logic/comparison, casts (int↔int, bool), `&/*` in disciplined
form, array indexing with bounds param, struct field access. No `goto`,
no `setjmp`, no VLAs, no globals mutated through aliases (read-only
`const` globals only), no `malloc/free` in v0.1 (arrays/locals only;
heap comes later as uniquely-owned `Vec`-like abstraction).

Pointer discipline (enforced by `validate` + oracle):
- `T*` params must be `__restrict__`-qualified or proven `noalias` by the
  oracle; no two live params may alias; no escaping (no storing a param
  pointer into a global or returning interior pointers beyond the
  `choose`-pattern with explicit backward function).
- No pointer arithmetic except `p[i]` / `*(p+i)` where `i` is bounded by
  an explicit length argument (`size_t n`) in the same function.
- No address-of-locals escaping the function; `&x` may only feed a
  `restrict` param call within the same scope.
- Functions returning `T*` must return exactly one of their `T*` inputs
  (borrow-return, like `choose`) or a fresh local that does not alias
  (rejected unless proven) — this triggers backward-function generation.

Admitted CIR ops (reject all else): `cir.func`, `cir.alloca/load/store`
(in functionalizable shape only), `cir.cast` (int/bool), `cir.binop/cmp/
unary`, `cir.br/cond_br`, `cir.scope/yield`, `cir.return/call`,
`cir.const`, `cir.get_member/get_element/ptr_stride` (bounded form),
`cir.if/while/for/ternary` as emitted by CIRGen.

## 5. Lean Model (`Circe.Base`) — No Memory

- Values, not addresses. C `int` → `BitVec n` (+ `Int` view for specs);
  structs → Lean `structure`s; arrays → `List`/`Array` with length
  invariant; pointers disappear (see §6).
- Partiality via `Result`: `def Result α := Except Panic α` where
  `Panic := Overflow | DivZero | OOB | AssertFail | Uninit`. No `Mem`,
  no `load_after_store` lemmas. UB in the subset maps to `Result.err`,
  and out-of-subset/aliasing never reaches Lean (rejected earlier).
- Loops: pure recursion with fuel or well-founded variant; `validate`
  requires a literal length bound or constant trip count in v0.1 to keep
  termination proofs trivial.
- Tactics: plain `simp/omega/bv_decide`; no memory framing tactics needed.

## 6. CoreIR + Forward/Backward Translation

```lean
inductive CType | void | bool | i (w:Nat) | u (w:Nat)
  | array (t:CType) | struct (fs:List CType)
-- note: no `ptr` in CoreIR values; pointers become ownership roles:
inductive BorrowRole | owned | mutBorrow (region:Nat) | sharedBorrow
inductive CStmt | skip | seq | let_ … | assign … | if … | while …
  | call … | return …
def Func := { name:String, args:List (String×CType×BorrowRole), … }
def Eval : CStmt → Env → Result (Env × Outcome) -- loan-based, value-only
```

`Eval` is Aeneas-style: environments map variables to **values with
loan/borrow bookkeeping** (no heap, no addresses). It is the spec for
`emit_correct`.

Translation schema (C examples):

```c
void incr(int *__restrict p) { *p = *p + 1; }
// → def incr_fwd (p : BitVec 32) : Result (BitVec 32) := checked_add p 1
// caller `incr(&y)` → `y ← incr_fwd y`

int *choose(bool b, int *__restrict x, int *__restrict y) { return b?x:y; }
// → def choose_fwd (b:Bool)(x y:BV32): Result BV32 := if b then ok x else ok y
// → def choose_back (b:Bool)(x y ret:BV32): Result (BV32×BV32) :=
//     if b then ok (ret,y) else ok (x,ret)
// caller: `z ← choose_fwd b x y; …; (x,y) ← choose_back b x y z'`

uint32_t sum(const uint32_t *a, size_t n) { … a[i] … }
// → def sum_fwd (a : List BV32)(n : Nat)(h : a.length = n) : Result BV32 := …
```

Every function taking `mutBorrow` params or returning a borrow gets a
backward function derived by inverting assignments along the body
(Aeneas §4.3); pure functions get forward only.

Emitter correctness:

```lean
def emitFunc : Func → Lean.Expr  -- forward (+ optional backward)
theorem emit_correct (f:Func) (ρ:Env) :
  evalLean (emitFunc f) ρ = Eval f ρ
-- corollaries: err preserved; return-value equivalence on ok paths
```

Proof by structural induction on `CStmt`, simulation between `Eval`
env and Lean lets; per-op lemmas required before admitting each op.

## 7. Phased Work Plan

### Phase 0 — Pins + corpus (acceptance: reproducible)
- Pin `llvm-project` SHA + CMake flags; pin Lean toolchain + Mathlib rev.
- Corpus `tests/c/*.c` → `tests/cir/*.cir`: `add`, `incr_ptr`,
  `choose_ptr`, `sum_array`, `struct_by_value`. Each with oracle verdict
  dump (`-fno-alias-report` equivalent) checked in.
- Freeze `docs/CIR_SUBSET.md` (§4) + `docs/OWNERSHIP.md` (discipline + examples).

### Phase 1 — Lean skeleton (acceptance: `lake build` green)
- Layout:
  ```
  Circe/Base.lean  CoreIR.lean  Eval.lean  Validator.lean
  Circe/Emit.lean  Parser/ (unverified Lean exe)  Oracle/ (verdict import)
  tests/ c/ cir/ oracle/ lean/ golden/
  docs/ PLAN.md CIR_SUBSET.md OWNERSHIP.md SEMANTICS.md VERIFYING.md
  ```
- CI: pinned clang build + `lake build`.

### Phase 2 — Base + Eval + lemmas (acceptance: lemmas compile)
- `Circe.Base`: `Result`, checked int ops, struct/array mappings.
- Loan-based `Eval` + `docs/SEMANTICS.md` table (CIR → CoreIR → Lean).
- Prove int-op correctness + env/loan well-formedness lemmas.

### Phase 3 — Emitter, 3 cases first (acceptance: E2E on `add`+`incr`)
- `emitFunc` for by-value `add` then `incr_fwd` (single `restrict` param).
- Prove `emit_correct` for that fragment; pretty-print
  `out/Add.lean`, `out/Incr.lean`; `lake build` checks them.
- Differential test: `lean --run` vs native on random inputs.

### Phase 4 — Borrow-returns + validator + oracle gate
  (acceptance: `choose` + `sum_array` translate and verify)
- Add `choose`-pattern (forward+backward synthesis) + bounded array loop.
- `validate` enforces §4 + requires oracle `noalias` verdict; failures
  emit precise rejections (`alias-reject`, `escape-reject`, `oob-possible`).
- Golden tests: `*.cir` → `*.expected.lean` + rejection-message checks.

### Phase 5 — Functional verification workflow (acceptance: 3 specs proved)
- Pattern: `theorem incr_correct`, `choose_lens_laws`, `sum_correct`
  (against `List.sum` spec) — all pure equations, no heap lemmas.
- `Circe.Tactics`: `cir_simp` for `Result`-bind + backward-function
  unfolding; document in `docs/VERIFYING.md`.

### Phase 6 — Hardening (acceptance: meaningful CI)
- Reject-suite: aliasing, escaping, `void*`, int-ptr casts, unbounded
  arithmetic — all must be rejected with actionable messages.
- Fuzz in-subset C → Lean `lean --run` vs native; mismatch = P0.
- Roadmap: uniquely-owned heap (`malloc` as `Vec`), C++-lite ctors
  (still no EH), shrinking oracle trust (Stacked-Borrows justification).

## 8. Definition of Done for v0.1

1. `lake build` passes with `emit_correct` for the full §4 subset.
2. Three pure functional-correctness theorems proved (§7 Phase 5).
3. Five golden C→CIR→Lean E2Es + differential random testing.
4. Reject-suite (§7 Phase 6) all rejected; no silent memory modeling.
5. Docs: `CIR_SUBSET.md`, `OWNERSHIP.md`, `SEMANTICS.md`, `VERIFYING.md`.

## 9. Risks

- **C has no borrow checker:** oracle may be conservative → high reject
  rate. Mitigate: strict-but-clear discipline (§4), measure reject rate on
  corpus early (Phase 0), expand oracle (CIR lifetime checker + `basicaa`
  + `__restrict__`) before expanding subset.
- **Oracle trust:** miscompiled `noalias` breaks soundness. Mitigate:
  Oracle verdicts checked in, differential testing, later formalization.
- **LLVM churn:** pin SHA, consume raw CIRGen, thin version-gated parser.
- **Backward-function blowup:** nested borrows/regions. Mitigate: v0.1
  allows single-region borrow-returns only (`choose`-shape); reject rest.
- **Termination:** recursion from loops. Mitigate: length-paired arrays +
  fuel/variant requirement in `validate`.

## 10. Next Actions (Phase 1 COMPLETE 2026-09-21; Phase 0 done 2026-09-20)

- [x] Record pinned `llvm-project` + Lean/Mathlib versions → `docs/PINS.md`
      (`32080ff` worktree pin, Lean 4.34.0; Mathlib `v4.34.0` → `5ed2965`).
- [x] Check in `tests/c/` corpus (add, incr_ptr, choose_ptr, sum_array,
      struct_by_value); native `clang -O0` driver passes (`corpus-native-OK`).
- [x] Capture `tests/cir/*.cir` goldens via `tools/emit-cir.sh` — all 5
      captured, `cir-opt` VERIFY-OK (see `docs/PINS.md` Status).
- [x] Freeze subset/discipline docs → `docs/CIR_SUBSET.md`, `docs/OWNERSHIP.md`
      (now with §6 translation schema as normative spec).
- [x] `lake init circe math` skeleton per §7 Phase 1 layout
      (`Circe/{Base,CoreIR,Eval,Validator,Emit,Parser,Oracle}.lean`,
      `lake build` green, CI via `lean_action_ci`).
- [x] Draft `Circe/Base.lean` (`Result` + checked `BV` ops) and `Eval` stub
      for `add`/`incr` fragment; validator gate closed-by-default stub.
- [x] `docs/SEMANTICS.md` (fragment table) + `docs/VERIFYING.md` (Phase 5
      pattern stub); `tests/{lean,golden}/` + `out/` dirs created.
