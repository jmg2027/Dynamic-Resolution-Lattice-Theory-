import E213.Lib.Math.Modulus.HasModulus
import E213.Lib.Math.Modulus.DiagonalHasModulus

/-!
# StrongModulus: bounded view-variation modulus (attempt (B) for E3)

Resolution direction (B) for `E3_modulus_kernel_deep_obstruction.md` —
213 form of the Bishop ε-N standard.  Strict strengthening of HasModulus:
not only orderProj stability but also bounded *ratio variation* of the view.

## Definition

`StrongModulus xs` : ∀ k ≥ 1, ∃ N, ∀ i, j ≥ N,
  |a_i/b_i - a_j/b_j| ≤ 1/k (cross-mult form).

## Significance

- Modulus combination for arithmetic such as addition is possible
  in the standard ε/2 form.
- A *strict* form of HasModulus — every StrongModulus is a HasModulus
  but not conversely.
-/

namespace E213.Lib.Math.Modulus.StrongModulus

open E213.Theory E213.Lens
open E213.Lens.Instances.AB

/-- **StrongModulus**: bounded ratio variation. -/
structure StrongModulus (xs : Nat → Raw) where
  N : Nat → Nat
  bound : ∀ k, k ≥ 1 → ∀ i j, i ≥ N k → j ≥ N k →
    (abLens.view (xs i)).1 * (abLens.view (xs j)).2 * k
      ≤ (abLens.view (xs i)).2 * (abLens.view (xs j)).1 * k
        + (abLens.view (xs i)).2 * (abLens.view (xs j)).2 ∧
    (abLens.view (xs i)).2 * (abLens.view (xs j)).1 * k
      ≤ (abLens.view (xs i)).1 * (abLens.view (xs j)).2 * k
        + (abLens.view (xs i)).2 * (abLens.view (xs j)).2



/-- **Diagonal sequence** (view (n+1, n+1)) is a StrongModulus instance.
    Constant ratio 1 → variation = 0 → trivial bound. -/
def diagonalStrongModulus (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) :
    StrongModulus xs where
  N := fun _ => 0
  bound := by
    intro k _ i j _ _
    rw [h i, h j]
    -- Goal: (i+1)*(j+1)*k ≤ (i+1)*(j+1)*k + (i+1)*(j+1) ∧ (symmetric)
    refine ⟨?_, ?_⟩
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_right _ _

end E213.Lib.Math.Modulus.StrongModulus
