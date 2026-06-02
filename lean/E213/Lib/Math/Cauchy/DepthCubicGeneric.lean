import E213.Meta.Nat.PolyNat
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.Cauchy.DepthQuadraticGeneric

/-!
# DepthCubicGeneric — every cubic discrete polynomial has divergence-depth 3

`cubic_polyDepth : ∀ A B C D, polyDepth 3 (fun n => A·n³ + B·n² + C·n + D)` — the cubic analog
of `DepthQuadraticGeneric.quadratic_polyDepth`, completing the depth-`d` = degree-`d` ladder to
degree 3.

The arithmetic crux is **`cube_eq`**: `n³` in the Newton basis,

    n³ = 6·binom n 3 + 6·binom n 2 + n      (= 6·C(n,3) + 6·C(n,2) + C(n,1)),

the subtraction-free cube analog of `sq_eq` (`n² = 2·binom n 2 + n`).  With it, `sq_eq` and
`binom_one`, the cubic equals `newton (D, A+B+C, 6A+2B, 6A) 3` pointwise (`cubic_eq`), whence
`newton_polyDepth` + `polyDepth_congr` give depth 3 — exactly the quadratic file's transfer,
one degree up.

Every multivariate `Nat` reorder here (the `cube_reorder` combine identity, and the two
collect-into-Newton-columns steps inside `cubic_eq`) is discharged in **one line** by the
multivariate reflection prover `Meta.Nat.PolyNatM` (`poly_idM`) — the `ring`-replacement that
`ac_rfl` (propext-dirty) cannot be over ℕ.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthCubicGeneric

open E213.Meta.Nat.PolyNat (poly_id)
open E213.Lib.Math.Cauchy.DepthPRecursiveInstances (binom newton newton_polyDepth)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Cauchy.DepthQuadraticGeneric (binom_one binom_succ_two sq_eq polyDepth_congr)
/-- The combine/reorder identity at the heart of `cube_eq`'s induction step — discharged in
    one line by the `ring_nat` reflection tactic (`Meta.Nat.PolyNatMTactic`). -/
theorem cube_reorder (T2 T3 n : Nat) :
    6*T3 + 6*T2 + n + 3*(2*T2 + n) + 3*n + 1 = 6*(T2 + T3) + 6*(n + T2) + (n+1) := by
  ring_nat

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

/-! ## §2 — every cubic discrete polynomial has divergence-depth 3 -/

/-- The Newton coefficients of `A·n³ + B·n² + C·n + D`: `(c 0, c 1, c 2, c 3) =
    (D, A+B+C, 6A+2B, 6A)` (from `cube_eq`, `sq_eq`, `binom_one`). -/
def cubicCoeff (A B C D : Nat) : Nat → Nat
  | 0   => D
  | 1   => A + B + C
  | 2   => 6*A + 2*B
  | _   => 6*A

/-- ★★ **A cubic is its Newton form.**  `A·n³ + B·n² + C·n + D = newton (cubicCoeff A B C D) 3
    n` pointwise.  The two multivariate reorders (reassociate `A·n·n·n` to `A·(n·n·n)`, then
    after substituting `cube_eq`/`sq_eq`/`binom_one` collect into the Newton columns) are each
    discharged in one `poly_idM`. -/
theorem cubic_eq (A B C D n : Nat) :
    A*n*n*n + B*n*n + C*n + D = newton (cubicCoeff A B C D) 3 n := by
  show A*n*n*n + B*n*n + C*n + D
     = D + (A+B+C) * binom n 1 + (6*A+2*B) * binom n 2 + 6*A * binom n 3
  rw [binom_one n]
  have reassoc : A*n*n*n + B*n*n + C*n + D = A*(n*n*n) + B*(n*n) + C*n + D := by ring_nat
  rw [reassoc, cube_eq n, sq_eq n]
  ring_nat

/-- ★★★ **Every cubic discrete polynomial has divergence-depth 3.**  For all `A B C D : ℕ`,
    `polyDepth 3 (fun n => A·n³ + B·n² + C·n + D)` — the cubic analog of
    `DepthQuadraticGeneric.quadratic_polyDepth`, completing the depth-`d` = degree-`d` ladder
    to degree 3.  Newton-form transfer (`cubic_eq` + `newton_polyDepth` + `polyDepth_congr`),
    with the multivariate reorders discharged by the `Meta.Nat.PolyNatM` reflection prover. -/
theorem cubic_polyDepth (A B C D : Nat) : polyDepth 3 (fun n => A*n*n*n + B*n*n + C*n + D) :=
  polyDepth_congr 3 _ _ (fun n => cubic_eq A B C D n) (newton_polyDepth (cubicCoeff A B C D) 3)

end E213.Lib.Math.Cauchy.DepthCubicGeneric
