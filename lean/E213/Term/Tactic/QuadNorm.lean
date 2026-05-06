/-!
# Tactic: `quad_norm`

Closes polynomial identities of the shape arising in
quadratic-extension norm-multiplicativity proofs
(`|uv|² = |u|²·|v|²` for ZI, Z2, ZOmega, ZSqrt-D, etc.).

Mechanism: AC-normalise products and sums via a 9-lemma `simp`
set (no `Mul.assoc`/`Add.assoc` infinite loops, all directed),
then close residual linear constraints over the resulting
atoms with `omega`.

Pure Lean 4 core: no `ring`, no Mathlib.

## Usage

```
open E213.Tactic
example (a b c d : Int) :
    (a*c - b*d)*(a*c - b*d) + (a*d + b*c)*(a*d + b*c)
  = (a*a + b*b) * (c*c + d*d) := by quad_norm
```

The `scoped macro` keeps the syntax out of clients that don't
explicitly `open E213.Tactic`.
-/

namespace E213.Tactic

scoped macro "quad_norm" : tactic => `(tactic|
  (simp only [Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add,
              Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
              Int.sub_eq_add_neg, Int.neg_mul, Int.mul_neg,
              Int.neg_neg]; omega))

end E213.Tactic
