/-
Circe.Emit.AliasCond — G3/S3 unknown-verdict branch-writer admission:
the `alias_cond` open contract (`if (c) *p += 1; *q += 2` over two
caller-aliased `int &` params, no `noalias` verdict).

No pure `(p,q,c)→(p′,q′)` function is sound here (G2): the re-read
of `q` after the branch store observes `p`'s write under aliasing.
The emission is therefore an open-contract `Func` over `pinnedCell`
params (S2 pins supply address + tag) with `mstore`/`mload` (S1/S3
`B2`) mirroring the source order, proved directly in `Mem` space
(`memTransfer_aliasCond` in `Circe.Transfer.Slice`: S2 pin facts →
`mstore`/`mload` equations → `decide (a = b)` split → the S0
inversions in `Circe.CondFrame`). The `void` return is modeled as a
zero word; the spec is the cell post, the return value is
meaningless.
-/
import Circe.Emit.Fragment

/-- Canonical CoreIR for `tests/cpp/alias_cond.cpp`
    (`void alias_cond(int &p, int &q, bool c)`: the branch-guarded
    `p`-store plus the unconditional `q`-store, both through pins). -/
def aliasCondFunc : Func :=
  ⟨"alias_cond",
   [{ name := "p", ty := .i 32, role := .pinnedCell },
    { name := "q", ty := .i 32, role := .pinnedCell },
    { name := "c", ty := .bool, role := .owned }],
   .void,
   .seq (.if_ (.var "c")
     (.mstore "p" (.lit (.u64 0))
       (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
     .skip)
   (.seq (.mstore "q" (.lit (.u64 0))
     (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
   (.return_ (.lit (.u32 0))))⟩

/-- Body check for the `matchFrag` arm, two-level so the giant
    `matchFrag` match stays shallow (F1 precedent): the branch
    condition name, the taken-branch `p`-store, and the rest (the
    `q`-store plus the void-modeling zero return) with the exact
    offsets and increments. -/
def isAliasCondBody : String → CStmt → CStmt → Bool
  | c, .mstore "p" (.lit (.u64 z1))
      (.add (.mload "p" (.lit (.u64 z2))) (.lit (.i32 one))),
    .seq (.mstore "q" (.lit (.u64 z3))
      (.add (.mload "q" (.lit (.u64 z4))) (.lit (.i32 two))))
         (.return_ (.lit (.u32 z))) =>
    c == "c" && z1 == 0 && z2 == 0 && z3 == 0 && z4 == 0 &&
    one == 1 && two == 2 && z == 0
  | _, _, _ => false
