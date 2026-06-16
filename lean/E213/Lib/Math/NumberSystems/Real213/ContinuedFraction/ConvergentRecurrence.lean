import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.Continuant
import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuantDeterminant
import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic

/-!
# The fundamental three-term recurrence of continued-fraction convergents

For the convergent-matrix product `M(l) = ∏ᵢ [[aᵢ,1],[1,0]]`, appending a partial
quotient `a` on the RIGHT (the convergent-building direction) satisfies the
classical **three-term recurrence**

  `pₙ = aₙ·pₙ₋₁ + pₙ₋₂`   (numerator, the `(1,1)`-entry `.a`)
  `qₙ = aₙ·qₙ₋₁ + qₙ₋₂`   (denominator, the `(2,1)`-entry `.c`).

Here `(M(l)).a = pₙ₋₁` and `(M(l)).b = pₙ₋₂` are carried as the consecutive
numerators, `(M(l)).c = qₙ₋₁` and `(M(l)).d = qₙ₋₂` the consecutive denominators.
Appending `[a]` multiplies on the right by `contMat a = [[a,1],[1,0]]`, and the
`mul` formula `mul M (contMat a)` gives `.a = M.a·a + M.b`, `.c = M.c·a + M.d`
— exactly Euler's recurrence (with `Int` commutativity to present it as `a·pₙ₋₁`).

Together with `ContinuantDeterminant` (`det = (−1)ⁿ`) and `ConvergentCoprime`
(`gcd(pₙ,qₙ)=1`) this closes the convergent-arithmetic core of CF theory.

∅-axiom: `decide`, `ring_intZ`, term-mode rewriting via `Int` simp-free lemmas
and `E213.Meta.Int213.mul_comm`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentRecurrence

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 mul)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.Continuant
  (contMat contMatProd contMatProd_append contMatProd_singleton)

/-- The right-append reduction: appending one quotient multiplies the product on
    the right by `contMat a`. -/
theorem contMatProd_snoc (l : List Nat) (a : Nat) :
    contMatProd (l ++ [a]) = mul (contMatProd l) (contMat a) := by
  rw [contMatProd_append, contMatProd_singleton]

/-- **Numerator recurrence** `pₙ = aₙ·pₙ₋₁ + pₙ₋₂`: the `(1,1)`-entry of the
    convergent-matrix product after appending the quotient `a`. -/
theorem cf_num_recurrence (l : List Nat) (a : Nat) :
    (contMatProd (l ++ [a])).a
      = (a : Int) * (contMatProd l).a + (contMatProd l).b := by
  rw [contMatProd_snoc]
  show (contMatProd l).a * (a : Int) + (contMatProd l).b * 1
      = (a : Int) * (contMatProd l).a + (contMatProd l).b
  rw [E213.Meta.Int213.mul_one, E213.Meta.Int213.mul_comm (contMatProd l).a (a : Int)]

/-- **Denominator recurrence** `qₙ = aₙ·qₙ₋₁ + qₙ₋₂`: the `(2,1)`-entry of the
    convergent-matrix product after appending the quotient `a`. -/
theorem cf_den_recurrence (l : List Nat) (a : Nat) :
    (contMatProd (l ++ [a])).c
      = (a : Int) * (contMatProd l).c + (contMatProd l).d := by
  rw [contMatProd_snoc]
  show (contMatProd l).c * (a : Int) + (contMatProd l).d * 1
      = (a : Int) * (contMatProd l).c + (contMatProd l).d
  rw [E213.Meta.Int213.mul_one, E213.Meta.Int213.mul_comm (contMatProd l).c (a : Int)]

/-! ## Smoke checks on small lists

`[2,3,4]`: numerators `p: 2,7,30`; denominators `q: 1,3,13` (with seed `p₋₂=1,q₋₂=0`).
The recurrence `30 = 4·7 + 2` and `13 = 4·3 + 1` is checked by `decide` on the
actual matrix entries. -/

/-- `(contMatProd [2,3]).a = 7`, `.b = 2`, and appending `4` gives `.a = 4·7+2 = 30`. -/
theorem smoke_num : (contMatProd ([2, 3] ++ [4])).a = 30
    ∧ (contMatProd [2, 3]).a = 7
    ∧ (contMatProd [2, 3]).b = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `(contMatProd [2,3]).c = 3`, `.d = 1`, and appending `4` gives `.c = 4·3+1 = 13`. -/
theorem smoke_den : (contMatProd ([2, 3] ++ [4])).c = 13
    ∧ (contMatProd [2, 3]).c = 3
    ∧ (contMatProd [2, 3]).d = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The recurrence verified concretely end-to-end on `[2,3] ++ [4]`. -/
theorem smoke_recurrence :
    (contMatProd ([2, 3] ++ [4])).a
      = 4 * (contMatProd [2, 3]).a + (contMatProd [2, 3]).b
    ∧ (contMatProd ([2, 3] ++ [4])).c
        = 4 * (contMatProd [2, 3]).c + (contMatProd [2, 3]).d := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentRecurrence
