import E213.Lib.Math.CartesianVsDisjoint.CartesianCheck
import E213.Lib.Math.CartesianVsDisjoint.DisjointVsProduct

/-!
# G45 Capstone — Cartesian vs Disjoint (∅-axiom)

5 cluster witnesses + total bundle.

Mingu's revised "Cartesian product" hypothesis verified:
  * `2²⁵ × 3²⁵ = 6²⁵ ≠ 5²⁵` (off by ~95×)
  * Closer than additive  but still wrong.
  * Correct interpretation: K_{3,2} = disjoint union (5 verts),
    NOT Cartesian product (6 verts).
-/

namespace E213.Lib.Math.CartesianVsDisjoint.Capstone

open E213.Lib.Math.CartesianVsDisjoint.CartesianCheck
  (cartesian_product_eq six_pow_25 five_pow_25
   cartesian_overshoots cartesian_neq_binomial sandwich_bound)
open E213.Lib.Math.CartesianVsDisjoint.DisjointVsProduct
  (disjoint_sum_card cartesian_product_card disjoint_neq_cartesian
   power_dichotomy strict_sep k32_disjoint_5)

/-- ★ **Cartesian arithmetic**: `2²⁵ × 3²⁵ = 6²⁵`. -/
theorem cartesian_arith_witness :
    (2 : Nat) ^ 25 * (3 : Nat) ^ 25 = (6 : Nat) ^ 25
    ∧ (6 : Nat) ^ 25 = 28430288029929701376 :=
  ⟨cartesian_product_eq, six_pow_25⟩

/-- ★ **Cartesian ≠ binomial**: `6²⁵ ≠ 5²⁵`. -/
theorem cartesian_neq_witness :
    (5 : Nat) ^ 25 < (6 : Nat) ^ 25
    ∧ (2 : Nat) ^ 25 * (3 : Nat) ^ 25 ≠ (5 : Nat) ^ 25 :=
  ⟨cartesian_overshoots, cartesian_neq_binomial⟩

/-- ★ **Sandwich bound**: `add < binomial < product`. -/
theorem sandwich_witness :
    (2 : Nat) ^ 25 + (3 : Nat) ^ 25 < (5 : Nat) ^ 25
    ∧ (5 : Nat) ^ 25 < (2 : Nat) ^ 25 * (3 : Nat) ^ 25 :=
  sandwich_bound

/-- ★ **Disjoint vs product distinction**: `5 = 3 + 2`,
    `6 = 3 × 2`. -/
theorem disjoint_product_witness :
    (3 : Nat) + 2 = 5
    ∧ (3 : Nat) * 2 = 6
    ∧ (5 : Nat) ≠ 6 :=
  ⟨disjoint_sum_card, cartesian_product_card,
   disjoint_neq_cartesian⟩

/-- ★★★ **Total witness** ★★★ — all three hypotheses with status. -/
theorem total_witness :
    (2 : Nat) ^ 25 + (3 : Nat) ^ 25 < (5 : Nat) ^ 25
    ∧ ((3 : Nat) + 2) ^ 25 = (5 : Nat) ^ 25
    ∧ (5 : Nat) ^ 25 < (2 : Nat) ^ 25 * (3 : Nat) ^ 25 :=
  ⟨sandwich_bound.1, rfl, sandwich_bound.2⟩

end E213.Lib.Math.CartesianVsDisjoint.Capstone
