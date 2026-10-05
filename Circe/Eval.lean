/-
Circe.Eval — loan-based, value-only ownership semantics (spec for
`emit_correct`).

Environments map variables to *values with loan/borrow bookkeeping*;
there is no heap and no addresses (Aeneas-style, see docs/PIPELINE.md).
Phase 4: `evalExpr` covers `lit`/`var`/`add` (signed `nsw`-checked,
over `i32`/`i64` — S3b) plus
`uadd`/`umul` (wrapping unsigned, over `u32`/`u64`), `ult` (unsigned
comparison, over `u32`/`u64`), `ueq` (bit equality, over
`u32`/`u64`/`i32`/`i64` — N4b: `cir.cmp eq` is signedness-blind), and `idx`
(bounded indexing, `OOB` on violation); `evalStmt` covers the full
loop-free fragment (`skip`/`seq`/`let_`/`assign`/`if_`/`return_`) plus
fuel-bounded `while_` (`EVAL_FUEL`; exhaustion is `AssertFail`, and
`validate` admits only bounded loops) plus S3a loop-scoped
`break_`/`continue_` (`broke`/`continued` outcomes: `while_` catches
them, escape from a body is `AssertFail`). `call` stays a legacy stub;
`callRet` carries S1 program calls (see the program layer below).
`bindArgs`/`evalFunc` give whole-function semantics; `evalFuncFuel`
exposes the fuel for induction (loop proofs generalize it).

Aggregator: values/expressions live in `Circe.Eval.Core`, statements
and programs in `Circe.Eval.Stmt`.
-/
import Circe.Eval.Core
import Circe.Eval.Stmt
