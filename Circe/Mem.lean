/-
Circe.Mem — addressful memory model for M3 (shrinking oracle trust).

M3a (C only): a flat block map with lightweight borrow tags, just strong
enough for our three uniqueness sources (`__restrict__` / `noalias`
attrs, disjoint `malloc` results, length-paired stride loops). No
retag/protect generality beyond what the admitted shapes express (see
docs/ROADMAP.md M3); full Stacked Borrows is an explicit non-goal.

State shape (locked): flat block map. `Mem` is a next-address counter +
an `Addr → Block` list-map; a block is a tag (= allocating epoch, so
fresh tags are distinct by construction) + live flag (mirrors the
`Vec32.freed` token: `live = !freed`) + word list. `Layout` maps bound
variable names to `(addr, expected tag)`: the borrow check is tag
equality + liveness + bounds on every access.

`memEval` mirrors `Eval` on the M3a fragment (call-free C leaves +
`sum` / `vec_alloc`): pure constructors delegate to `evalExpr` with
`Mem`/`Layout` untouched; `idx` / `vget` resolve the layout, check the
tag, and cross-check the memory read against the value-level read (both
must agree, else `AssertFail`); `vset` / `vfree` update the value *and*
the block in lockstep (either side failing is loud). `Eval` itself is
untouched.

The transfer `oracleNoalias → memEval = Eval` lands here as the M3c
conjecture (`m3c_transfer` axiom); M3a proves the per-leaf instances
(`memTransfer_add/incr/sum/vec`) as evidence. `oracleNoalias` is the
entry-footprint disjointness the M3b `derivedNoalias` check will imply.

Aggregator: the model lives in `Circe.Mem.Model`, transfer instances
in `Circe.Mem.Agree`.
-/
import Circe.Mem.Model
import Circe.Mem.Agree
