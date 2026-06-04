import E213.Lib.Math.Algebra.Polynomial213.Core
import E213.Lib.Math.Algebra.Polynomial213.Sound
import E213.Lib.Math.Algebra.Polynomial213.Ineq

/-! Spec-as-code umbrella for `Lib.Math.Polynomial213` — single-import entry.

Coefficient-array polynomial reflection over `Nat` (∅-axiom).  Closes
Wallis/Pell-style polynomial identities via `rfl` after both sides are
encoded as `Poly`.

## Sub-modules

  * `Core`   — `Poly`, `eval`, `C`, `X`, `add`, `scale`, `shift`, `mul`,
                `trim` (type defs + Horner evaluation)
  * `Sound`  — `eval_*` soundness lemmas (each op commutes with `eval`)
  * `Ineq`   — `eval_le_of_add`, `eval_lt_of_add_succ` witness pattern
                for polynomial inequalities

Importing `Polynomial213` (this file) pulls in the full stack;
downstream may also pin to `Polynomial213.Sound` or `.Ineq` directly.
-/
