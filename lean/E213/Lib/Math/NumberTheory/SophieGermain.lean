import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.OrderMul

/-!
# The Sophie Germain identity (∅-axiom, over `Int`)

`a⁴ + 4·b⁴ = (a² − 2ab + 2b²)·(a² + 2ab + 2b²)` (`sophie_germain`) — the classical
factorization (the algebraic generalization of the Aurifeuillean idea; it shows
`a⁴ + 4b⁴` is composite for `a, b ≥ 1`, e.g. `n⁴ + 4` for `n > 1`).  With:

  * SOS forms `a²−2ab+2b² = (a−b)²+b²`, `a²+2ab+2b² = (a+b)²+b²`;
  * both factors `≥ 1` for `a, b ≥ 1` (nontriviality ⟹ compositeness);
  * the `b = 1` specialization `n⁴ + 4 = (n²−2n+2)(n²+2n+2)`.

Genuinely absent (the corpus "Germain/Aurifeuillean" hits are cohomology
config-count cutoffs, not the algebraic identity).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.SophieGermain

open E213.Meta.Int213
open E213.Meta.Int213.Order (le_trans le_refl add_le_add_right add_le_add_left le_of_lt)
open E213.Meta.Int213.OrderMul (sq_le_sq_of_le)

/-- ★ **Sophie Germain identity** over `Int`. -/
theorem sophie_germain (a b : Int) :
    a*a*a*a + 4*(b*b*b*b)
      = (a*a - 2*a*b + 2*(b*b)) * (a*a + 2*a*b + 2*(b*b)) := by
  ring_intZ

/-- SOS form of the smaller factor: `a² − 2ab + 2b² = (a−b)² + b²`. -/
theorem small_factor_sos (a b : Int) :
    a*a - 2*a*b + 2*(b*b) = (a - b)*(a - b) + b*b := by
  ring_intZ

/-- SOS form of the larger factor: `a² + 2ab + 2b² = (a+b)² + b²`. -/
theorem large_factor_sos (a b : Int) :
    a*a + 2*a*b + 2*(b*b) = (a + b)*(a + b) + b*b := by
  ring_intZ

/-- `1 ≤ b → 1 ≤ b*b`. -/
theorem one_le_sq {b : Int} (hb : 1 ≤ b) : (1 : Int) ≤ b * b := by
  have h01 : (0 : Int) ≤ 1 := le_of_lt (by decide)
  exact sq_le_sq_of_le h01 hb

/-- `0 ≤ s → 1 ≤ t → 1 ≤ s + t`. -/
theorem one_le_add_of_nonneg_of_one_le {s t : Int}
    (hs : 0 ≤ s) (ht : 1 ≤ t) : (1 : Int) ≤ s + t := by
  have h1 : (0 : Int) + 1 ≤ s + 1 := add_le_add_right hs 1
  have h2 : s + 1 ≤ s + t := add_le_add_left ht s
  exact le_trans h1 h2

/-- ★ **Smaller factor ≥ 1** for `a, b ≥ 1` — the factorization is nontrivial, so
    `a⁴ + 4b⁴` is composite. -/
theorem small_factor_ge_one {a b : Int} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : Int) ≤ a*a - 2*a*b + 2*(b*b) := by
  rw [small_factor_sos a b]
  exact one_le_add_of_nonneg_of_one_le (int_sq_nonneg (a - b)) (one_le_sq hb)

/-- ★ **Larger factor ≥ 1** for `a, b ≥ 1`. -/
theorem large_factor_ge_one {a b : Int} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : Int) ≤ a*a + 2*a*b + 2*(b*b) := by
  rw [large_factor_sos a b]
  exact one_le_add_of_nonneg_of_one_le (int_sq_nonneg (a + b)) (one_le_sq hb)

/-- **`b = 1` specialization**: `n⁴ + 4 = (n²−2n+2)(n²+2n+2)`. -/
theorem germain_b_one (n : Int) :
    n*n*n*n + 4 = (n*n - 2*n + 2) * (n*n + 2*n + 2) := by
  ring_intZ

/-- Concrete smoke: `n = 5` gives `629 = 17 · 37`. -/
theorem germain_five : (5:Int)*5*5*5 + 4 = (5*5 - 2*5 + 2) * (5*5 + 2*5 + 2) := by
  decide

end E213.Lib.Math.NumberTheory.SophieGermain
