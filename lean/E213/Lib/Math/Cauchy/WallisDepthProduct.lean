import E213.Lib.Math.Cauchy.FiniteDepthAlgebra

/-!
# WallisDepthProduct — π's degree-4 ratio from the finite-depth *ring*

`DepthPRecursiveInstances` pins π's Wallis convergent coefficients
`4(n+1)²` and `(2n+1)(2n+3)` at depth 2 each, but left the *product* — π's
cross-determinant ratio, a degree-4 polynomial — to "more nonlinear-`Nat`
expansion".  The finite-depth **ring** (`FiniteDepthAlgebra.polyDepthZ_mul`) closes
that residual step with no expansion at all: each coefficient is a product of two
affine factors (depth 1), so depth `2`; their product is depth `4`.

> ★★★ `pi_ratio_polyDepthZ` : π's cross-determinant ratio
> `4(n+1)²·(2n+1)(2n+3)` has `polyDepthZ 4`.

All ∅-axiom.
-/

namespace E213.Lib.Math.Cauchy.WallisDepthProduct

open E213.Lib.Math.Cauchy.NewtonGregory (diffZ liftKZ polyDepthZ sub_self_zero)
open E213.Lib.Math.Cauchy.FiniteDepthAlgebra (add_sub_add polyDepthZ_mul)
open E213.Meta.Int213
  (add_comm add_assoc add_neg_cancel zero_add mul_add mul_one)

/-- `(a + b) − b = a` (pure). -/
theorem add_sub_cancel_r (a b : Int) : (a + b) - b = a := by
  rw [Int.sub_eq_add_neg, add_assoc, add_neg_cancel, Int.add_zero]

/-- The forward difference of an affine `ℤ`-sequence is its constant slope. -/
theorem diffZ_affine (a b : Int) (n : Nat) :
    diffZ (fun m => a * (m : Int) + b) n = a := by
  show a * ((n + 1 : Nat) : Int) + b - (a * (n : Nat) + b) = a
  show a * ((n : Int) + 1) + b - (a * (n : Int) + b) = a
  rw [mul_add, mul_one, add_assoc, add_sub_add, sub_self_zero, add_sub_cancel_r,
      zero_add]

/-- ★ **Affine sequences have depth 1.**  `polyDepthZ 1 (a·n + b)`. -/
theorem polyDepthZ_affine (a b : Int) : polyDepthZ 1 (fun m => a * (m : Int) + b) := by
  intro n
  show diffZ (fun m => a * (m : Int) + b) n = diffZ (fun m => a * (m : Int) + b) 0
  rw [diffZ_affine a b n, diffZ_affine a b 0]

/-- π's Wallis **denominator** step coefficient `(2n+1)(2n+3)` has `polyDepthZ 2`
    — the product of two affine (depth-1) factors, via `polyDepthZ_mul`.  No
    nonlinear-`ℤ` expansion. -/
theorem wallisDen_polyDepthZ :
    polyDepthZ 2 (fun n => (2 * (n : Int) + 1) * (2 * (n : Int) + 3)) :=
  polyDepthZ_mul (polyDepthZ_affine 2 1) (polyDepthZ_affine 2 3)

/-- π's Wallis **numerator** step coefficient `4(n+1)² = (4n+4)(n+1)` has
    `polyDepthZ 2` (product of two affine factors). -/
theorem wallisNum_polyDepthZ :
    polyDepthZ 2 (fun n => (4 * (n : Int) + 4) * (1 * (n : Int) + 1)) :=
  polyDepthZ_mul (polyDepthZ_affine 4 4) (polyDepthZ_affine 1 1)

/-- ★★★ **π's cross-determinant ratio has depth exactly the product degree, 4.**
    The ratio is the product of the two degree-2 Wallis step coefficients; the
    finite-depth ring gives `polyDepthZ (2+2) = polyDepthZ 4` directly — closing the
    "residual nonlinear-`Nat` expansion" left open in `DepthPRecursiveInstances`. -/
theorem pi_ratio_polyDepthZ :
    polyDepthZ 4 (fun n => ((4 * (n : Int) + 4) * (1 * (n : Int) + 1))
                          * ((2 * (n : Int) + 1) * (2 * (n : Int) + 3))) :=
  polyDepthZ_mul wallisNum_polyDepthZ wallisDen_polyDepthZ

end E213.Lib.Math.Cauchy.WallisDepthProduct
