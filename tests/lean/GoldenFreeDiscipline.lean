-- Golden test for M1d: free discipline (leak allowed, double-free loud).
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenFreeDiscipline.lean`
-- 1. Corpus pipeline: `tests/cir/vec_alloc_leak.cir` (real CIRGen output for
--    `tests/c/vec_alloc_leak.c`, which never frees) validates and emits the
--    `VecAlloc` body (`vecFillSumU32 n.toNat`, byte-identical modulo the
--    function name): the relaxation is validator-side only, the same
--    canonical `vecFunc` is emitted.
-- 2. Stripped-free acceptance: each of the four heap shapes with every
--    `cir.call @free(` line removed validates to the byte-identical golden
--    (plus a partial-leak `vec_copy_sum` with one of two `free`s dropped).
-- 3. Rejection: text-level double-`free` (`free > malloc`) still rejects.
-- 4. Token checks: `Base`-level double-`free` / use-after-`free`
--    (`vecFree`/`vecGet`/`vecSet`/`vecRealloc` on a freed `Vec32`,
--    `vecFree64`/`vecGet64` on a freed `Vec64`) are `AssertFail`, never
--    silently modeled.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

/-- Real leak corpus: validates and emits the `VecAlloc` body under its own
    name (validator-side-only relaxation: same canonical `Func`). -/
def checkLeakPipeline (verdicts : List OracleFact) : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_alloc_leak.cir"
  let want ← IO.FS.readFile "tests/golden/VecAlloc.lean"
  let oracle ← match lookupOracle verdicts "vec_alloc_leak" with
    | none => throw (IO.userError "no oracle fact for vec_alloc_leak")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if !containsSubstr got "vec_alloc_leak_fwd" then
      throw (IO.userError "leak emission missing vec_alloc_leak_fwd")
    if !containsSubstr got "vecFillSumU32 n.toNat" then
      throw (IO.userError "leak emission missing vecFillSumU32 body")
    if got.replace "vec_alloc_leak" "vec_alloc" != want then
      throw (IO.userError "leak emission differs from VecAlloc golden modulo name")
    IO.println "PASS pipeline vec_alloc_leak"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_alloc_leak: {msg}")

/-- Drop every `free` call-site line (leak the whole shape). -/
def stripFreeLines (text : String) : String :=
  "\n".intercalate
    ((text.splitOn "\n").filter (fun line => !containsSubstr line "cir.call @free("))

/-- Drop only the first `free` call-site line (partial leak). -/
def stripFirstFreeLine (text : String) : String :=
  let lines := text.splitOn "\n"
  let rec go : List String → Bool → List String
    | [], _ => []
    | l :: ls, false =>
      if containsSubstr l "cir.call @free(" then go ls true else l :: go ls false
    | l :: ls, true => l :: go ls true
  "\n".intercalate (go lines false)

/-- Full-leak variant of a real shape validates to the byte-identical golden
    (same canonical `Func`: relaxation is validator-side only). -/
def checkStripLeak (cir golden name : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  let want ← IO.FS.readFile golden
  let oracle : OracleFact := ⟨name, .unknown⟩
  match runPipeline (stripFreeLines text) oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError s!"strip-leak {name}: emission differs from golden")
    IO.println s!"PASS strip-leak {name}"
    pure 1
  | .error msg =>
    throw (IO.userError s!"strip-leak {name} unexpectedly rejected: {msg}")

/-- Partial-leak `vec_copy_sum` (one of two `free`s dropped) still validates
    to the byte-identical golden. -/
def checkPartialLeak : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_copy_sum.cir"
  let want ← IO.FS.readFile "tests/golden/VecCopySum.lean"
  let oracle : OracleFact := ⟨"vec_copy_sum", .unknown⟩
  match runPipeline (stripFirstFreeLine text) oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError "partial-leak vec_copy_sum: emission differs from golden")
    IO.println "PASS partial-leak vec_copy_sum"
    pure 1
  | .error msg =>
    throw (IO.userError s!"partial-leak vec_copy_sum unexpectedly rejected: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectFD (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-suite-fd: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-suite-fd: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-suite-fd: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-fd {name} [{code}]"
    pure 1

/-- Token-level check: a `Base` heap op on a freed block is `AssertFail`. -/
def checkTokenFD {α : Type} [Repr α] (name : String) (r : Result α) : IO Nat := do
  match r with
  | .error .AssertFail =>
    IO.println s!"PASS token-fd {name} [AssertFail]"
    pure 1
  | e =>
    throw (IO.userError s!"token-fd {name}: expected AssertFail, got {(repr e).pretty}")

/-- One `malloc`, two `free`s: double-`free` stays loud after M1d. -/
def advDoubleFreeFD : String :=
  "module {\n  cir.func @dfd(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkLeakPipeline verdicts
  passed := passed + c1
  let c2 ← checkStripLeak "tests/cir/vec_alloc.cir" "tests/golden/VecAlloc.lean" "vec_alloc"
  passed := passed + c2
  let c3 ← checkStripLeak "tests/cir/vec_copy_sum.cir" "tests/golden/VecCopySum.lean" "vec_copy_sum"
  passed := passed + c3
  let c4 ← checkStripLeak "tests/cir/vec_alloc_u64.cir" "tests/golden/VecAllocU64.lean" "vec_alloc_u64"
  passed := passed + c4
  let c5 ← checkStripLeak "tests/cir/vec_realloc.cir" "tests/golden/VecRealloc.lean" "vec_realloc"
  passed := passed + c5
  let c6 ← checkPartialLeak
  passed := passed + c6
  let c7 ← checkRejectFD "dfd" advDoubleFreeFD .unknown
    "out-of-subset" "double-`free`"
  passed := passed + c7
  let c8 ← checkTokenFD "double-free" (vecFree ⟨[1, 2], true⟩)
  passed := passed + c8
  let c9 ← checkTokenFD "use-after-free-get" (vecGet ⟨[1, 2], true⟩ 0)
  passed := passed + c9
  let c10 ← checkTokenFD "use-after-free-set" (vecSet ⟨[1, 2], true⟩ 0 9)
  passed := passed + c10
  let c11 ← checkTokenFD "use-after-free-realloc" (vecRealloc ⟨[1, 2], true⟩ 4)
  passed := passed + c11
  let c12 ← checkTokenFD "double-free-64" (vecFree64 ⟨[1, 2], true⟩)
  passed := passed + c12
  let c13 ← checkTokenFD "use-after-free-get-64" (vecGet64 ⟨[1, 2], true⟩ 0)
  passed := passed + c13
  IO.println s!"GOLDENFREEDISCIPLINE-OK passed={passed}"
