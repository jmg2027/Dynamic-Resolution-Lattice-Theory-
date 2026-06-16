import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.Continuant
import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntM
import E213.Meta.Int213.PolyIntMTactic

/-!
# Euler's continuant determinant identity (the fundamental recurrence of CFs)

`det(∏ᵢ [[aᵢ,1],[1,0]]) = (−1)ⁿ` — the determinant of the convergent-matrix
product of the continued fraction `[a₁;a₂,…,aₙ]` is `(−1)ⁿ`.  Unpacked to the
matrix entries (whose `(1,1)`-entry is the continuant `K[a₁..aₙ]` and `(2,1)`-entry
is `K[a₂..aₙ]`, per `Continuant.continuant_eq_contMatProd`) this is the
**cross-determinant** identity
`M.a·M.d − M.b·M.c = (−1)ⁿ`,
i.e. the classical relation between consecutive convergents
`pₙ qₙ₋₁ − pₙ₋₁ qₙ = (−1)ⁿ⁺¹` — the source of convergent **coprimality** and of the
`|x − pₙ/qₙ| < 1/qₙ²` Diophantine-approximation bound.

This is the one classical continuant theorem absent from `Continuant.lean` (which
built the continuant, its `Mat2` presentation, monotonicity, reversal, and trace
identity).  Proof skeleton: define `detM` on `Mat2`, show it is multiplicative
(`detM_mul`, by `ring_intZ`), that each `contMat a` has determinant `−1`, then a
length-induction gives `(−1)ⁿ`.  Corollary `continuant_det_unit`: the
cross-determinant is a unit `±1` (the coprimality witness).

All ∅-axiom: `decide`, `ring_intZ`, term-mode `Int213.mul_comm`, and structural
induction only — no `omega`/`simp [..]`/propext-leaking `rw…at`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuantDeterminant

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 mul I2)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.Continuant
open E213.Meta.Int213.PolyIntM (powInt)

/-- Determinant of a `Mat2`. -/
def detM (M : Mat2) : Int := M.a * M.d - M.b * M.c

/-- `det I2 = 1`. -/
theorem detM_I2 : detM I2 = 1 := by decide

/-- **Determinant is multiplicative**: `det (M·N) = det M · det N`. -/
theorem detM_mul (M N : Mat2) : detM (mul M N) = detM M * detM N := by
  show (M.a * N.a + M.b * N.c) * (M.c * N.b + M.d * N.d)
       - (M.a * N.b + M.b * N.d) * (M.c * N.a + M.d * N.c)
     = (M.a * M.d - M.b * M.c) * (N.a * N.d - N.b * N.c)
  ring_intZ

/-- Each continuant matrix `[[a,1],[1,0]]` has determinant `−1`. -/
theorem detM_contMat (a : Nat) : detM (contMat a) = -1 := by
  show (a : Int) * 0 - 1 * 1 = -1
  rw [Int.mul_zero, Int.one_mul]
  decide

/-- **Euler's continuant determinant identity (matrix form)**:
    `det (∏ᵢ [[aᵢ,1],[1,0]]) = (−1)ⁿ` where `n = length l`. -/
theorem detM_contMatProd : ∀ l : List Nat,
    detM (contMatProd l) = powInt (-1) l.length
  | [] => detM_I2
  | a :: t => by
      show detM (mul (contMat a) (contMatProd t)) = powInt (-1) (t.length + 1)
      rw [detM_mul, detM_contMat, detM_contMatProd t]
      show (-1 : Int) * powInt (-1) t.length = powInt (-1) t.length * (-1)
      exact E213.Meta.Int213.mul_comm _ _

/-- ★ **Euler's continuant identity (entry form)**: for the continuant matrix product
    `M = ∏ᵢ [[aᵢ,1],[1,0]]`, the cross-product of its entries satisfies
    `M.a · M.d − M.b · M.c = (−1)ⁿ`.

    The `(1,1)`-entry is `K[a₁..aₙ]`, the `(2,1)`-entry is `K[a₂..aₙ]`; the `(1,2)`/`(2,2)`
    entries are the reversed-word "previous" continuants.  This is the **fundamental recurrence
    relation of continued fractions**: consecutive convergents `pₙ/qₙ`, `pₙ₋₁/qₙ₋₁` satisfy
    `pₙ qₙ₋₁ − pₙ₋₁ qₙ = (−1)ⁿ⁺¹`, the source of their coprimality and the
    `|x − pₙ/qₙ| < 1/qₙ²` approximation bound. -/
theorem continuant_cross_det (l : List Nat) :
    (contMatProd l).a * (contMatProd l).d
      - (contMatProd l).b * (contMatProd l).c
    = powInt (-1) l.length :=
  detM_contMatProd l

/-- `powInt (-1) n` is a unit `±1`. -/
theorem powNegOne_unit : ∀ n : Nat, powInt (-1) n = 1 ∨ powInt (-1) n = -1
  | 0 => Or.inl rfl
  | n + 1 => by
      show powInt (-1) n * (-1) = 1 ∨ powInt (-1) n * (-1) = -1
      cases powNegOne_unit n with
      | inl h => exact Or.inr (by rw [h]; decide)
      | inr h => exact Or.inl (by rw [h]; decide)

/-- **Unit cross-determinant** (the classical consequence): the cross-determinant of the
    continuant matrix product is a unit `±1`.  This is exactly what forces consecutive
    continuants/convergents to be **coprime** (any common divisor divides `±1`). -/
theorem continuant_det_unit (l : List Nat) :
    (contMatProd l).a * (contMatProd l).d
      - (contMatProd l).b * (contMatProd l).c = 1
    ∨ (contMatProd l).a * (contMatProd l).d
        - (contMatProd l).b * (contMatProd l).c = -1 := by
  rw [continuant_cross_det]
  exact powNegOne_unit l.length

/-! ## Concrete checks: K cross-determinant = ±1 -/

/-- `det(contMatProd [1,1]) = (−1)² = 1`, `det(contMatProd [1,1,1]) = (−1)³ = −1`. -/
theorem cross_det_examples :
    (contMatProd [1, 1]).a * (contMatProd [1, 1]).d
      - (contMatProd [1, 1]).b * (contMatProd [1, 1]).c = 1
    ∧ (contMatProd [1, 1, 1]).a * (contMatProd [1, 1, 1]).d
        - (contMatProd [1, 1, 1]).b * (contMatProd [1, 1, 1]).c = -1 := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuantDeterminant
