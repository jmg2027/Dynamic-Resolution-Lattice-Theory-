/-!
# Cartesian Product Check (∅-axiom)

Mingu's revised hypothesis:
> "2^25 × 3^25 = 5^25, 전부 카르테시안 곱"

**Status: Numerically wrong by factor ~95.**

Calculation:
  * `2²⁵ × 3²⁵ = (2 · 3)²⁵ = 6²⁵`
  * `6²⁵ ≈ 2.84 × 10¹⁹`
  * `5²⁵ ≈ 2.98 × 10¹⁷`
  * Ratio `6²⁵ / 5²⁵ = 1.2²⁵ ≈ 95.4`

The Cartesian product hypothesis is closer to right than the
additive `3²⁵ + 2²⁵` hypothesis (off by ~10⁸ in G44), but still
incorrect by about 2 orders of magnitude.

The CORRECT decomposition remains the **binomial expansion**
`(3 + 2)²⁵ = 5²⁵` from G44.

**Why does Cartesian product fail?**
  * A Cartesian product `N_S × N_T = 3 × 2 = 6` would label
    vertices by pairs `(s, t) ∈ S × T`, giving a 6-vertex graph.
  * But `K_{3,2}` is the **bipartite graph** with `5 = 3 + 2`
    vertices (disjoint union), NOT 6 (Cartesian product).
  * So the substrate is `disjoint sum`, not `direct product`.
-/

namespace E213.Lib.Math.Geometry.CartesianVsDisjoint.CartesianCheck

/-- ★ **Cartesian product expansion**: `2²⁵ · 3²⁵ = 6²⁵`
    (direct kernel `decide`, ∅-axiom). -/
theorem cartesian_product_eq :
    (2 : Nat) ^ 25 * (3 : Nat) ^ 25 = (6 : Nat) ^ 25 := by decide

/-- ★ **`6²⁵` closed form**. -/
theorem six_pow_25 :
    (6 : Nat) ^ 25 = 28430288029929701376 := by decide

/-- ★ **`5²⁵` closed form** (recall ). -/
theorem five_pow_25 :
    (5 : Nat) ^ 25 = 298023223876953125 := rfl

/-- ★ **Strict inequality**: `5²⁵ < 6²⁵`. -/
theorem cartesian_overshoots :
    (5 : Nat) ^ 25 < (6 : Nat) ^ 25 := by decide

/-- ★ **Numerical check**: `2²⁵ × 3²⁵ ≠ 5²⁵`. -/
theorem cartesian_neq_binomial :
    (2 : Nat) ^ 25 * (3 : Nat) ^ 25 ≠ (5 : Nat) ^ 25 := by decide

/-- ★ **Both decompositions wrong, only binomial right**:
    `2²⁵ + 3²⁵ < 5²⁵ < 2²⁵ · 3²⁵`. -/
theorem sandwich_bound :
    (2 : Nat) ^ 25 + (3 : Nat) ^ 25 < (5 : Nat) ^ 25
    ∧ (5 : Nat) ^ 25 < (2 : Nat) ^ 25 * (3 : Nat) ^ 25 := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

end E213.Lib.Math.Geometry.CartesianVsDisjoint.CartesianCheck
