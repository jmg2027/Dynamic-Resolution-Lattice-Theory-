import E213.Meta.Nat.PolyNat
import E213.Lib.Math.Cauchy.DepthQuadraticGeneric

/-!
# DepthCubicGeneric — the cube in the Newton (binomial) basis

The degree-3 step toward `∀ A B C D, polyDepth 3 (fun n => A·n³ + B·n² + C·n + D)` (the cubic
analog of `DepthQuadraticGeneric.quadratic_polyDepth`).  The arithmetic crux — and the one
genuinely new lemma — is **`cube_eq`**: `n³` in the Newton basis,

    n³ = 6·binom n 3 + 6·binom n 2 + n      (= 6·C(n,3) + 6·C(n,2) + C(n,1)),

the subtraction-free cube analog of `sq_eq` (`n² = 2·binom n 2 + n`).  Its induction step
reduces, via the univariate `(n+1)³ = n³+3n²+3n+1` (`poly_id`) and `sq_eq`, to the
combine/reorder identity `cube_reorder`, proved ∅-axiom over ℕ with the PURE
`NatHelper.{add_mul, mul_assoc}` + `Nat.add_right_comm` (no `ring`/`ac_rfl`, which are
propext-dirty).

With `cube_eq`, `sq_eq`, `binom_one` the cubic equals `newton (D, A+B+C, 6A+2B, 6A) 3`
pointwise, whence `newton_polyDepth` + `polyDepth_congr` give depth 3 — exactly the quadratic
file's transfer, one degree up.  The remaining assembly (`cubic_eq` + `cubic_polyDepth`) is a
purely mechanical 7-term multivariate `Nat` reorder (no new ideas, no `ring` available); it is
left for a follow-up rather than ground out by hand here.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthCubicGeneric

open E213.Meta.Nat.PolyNat (poly_id)
open E213.Lib.Math.Cauchy.DepthPRecursiveInstances (binom newton newton_polyDepth)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Cauchy.DepthQuadraticGeneric (binom_one binom_succ_two sq_eq polyDepth_congr)
open E213.Tactic.NatHelper (add_mul mul_assoc)

/-- The combine/reorder identity at the heart of `cube_eq`'s induction step. -/
theorem cube_reorder (T2 T3 n : Nat) :
    6*T3 + 6*T2 + n + 3*(2*T2 + n) + 3*n + 1 = 6*(T2 + T3) + 6*(n + T2) + (n+1) := by
  have h6 : (6:Nat) * n = 3*n + 3*n := by rw [← add_mul]
  have h62 : (3:Nat) * (2*T2) = 6*T2 := by rw [← mul_assoc]
  rw [Nat.mul_add 3 (2*T2) n, h62, Nat.mul_add 6 T2 T3, Nat.mul_add 6 n T2, h6,
      -- flatten LHS group (6T2+3n) and RHS groups (3n+3n), (n+1) to left-assoc
      ← Nat.add_assoc (6*T3 + 6*T2 + n) (6*T2) (3*n),
      ← Nat.add_assoc (6*T2 + 6*T3) (3*n + 3*n) (6*T2),
      ← Nat.add_assoc (6*T2 + 6*T3) (3*n) (3*n),
      ← Nat.add_assoc (6*T2 + 6*T3 + 3*n + 3*n + 6*T2) n 1,
      -- sort LHS: bubble the lone `n` right past 6T2, 3n, 3n
      Nat.add_right_comm (6*T3 + 6*T2) n (6*T2),
      Nat.add_right_comm (6*T3 + 6*T2 + 6*T2) n (3*n),
      Nat.add_right_comm (6*T3 + 6*T2 + 6*T2 + 3*n) n (3*n),
      -- sort RHS: swap the leading 6T2,6T3, then bubble the two 3n past the trailing 6T2
      Nat.add_comm (6*T2) (6*T3),
      Nat.add_right_comm (6*T3 + 6*T2 + 3*n) (3*n) (6*T2),
      Nat.add_right_comm (6*T3 + 6*T2) (3*n) (6*T2)]

/-- ★★ **The cube in the Newton (binomial) basis**: `n³ = 6·binom n 3 + 6·binom n 2 + n`
    — the subtraction-free `n³ = 6·C(n,3) + 6·C(n,2) + C(n,1)`.  Induction via the univariate
    `(n+1)³ = n³+3n²+3n+1` (`poly_id`) + `sq_eq` + `cube_reorder`. -/
theorem cube_eq : ∀ n, n*n*n = 6 * binom n 3 + 6 * binom n 2 + n
  | 0     => rfl
  | n + 1 => by
      have cube_succ : (n+1)*(n+1)*(n+1) = n*n*n + 3*(n*n) + 3*n + 1 :=
        poly_id
          (.mul (.mul (.add .X (.C 1)) (.add .X (.C 1))) (.add .X (.C 1)))
          (.add (.add (.add (.mul (.mul .X .X) .X) (.mul (.C 3) (.mul .X .X)))
                    (.mul (.C 3) .X)) (.C 1))
          rfl n
      show (n+1)*(n+1)*(n+1) = 6 * binom (n+1) 3 + 6 * binom (n+1) 2 + (n+1)
      rw [cube_succ, cube_eq n, sq_eq n,
          show binom (n+1) 3 = binom n 2 + binom n 3 from rfl, binom_succ_two n]
      exact cube_reorder (binom n 2) (binom n 3) n

end E213.Lib.Math.Cauchy.DepthCubicGeneric
