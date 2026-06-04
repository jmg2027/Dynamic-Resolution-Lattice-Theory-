import E213.Lib.Math.Geometry.GenerationRule.GenerationCount

/-!
# Clarifying `(2+3)²⁵`: 25 is the orthogonal direction (∅-axiom)

Mingu's question:
> "(2+3)^25의 의미가 2,3 둘이 별개의 직교하는 축으로 올라가는게
>  아니라 2+3인거가 직교하는 축으로 올라가는건가?"

**Answer: neither, but closer to the second.**

Structurally:
  * The **25 levels** are the orthogonal direction — 25 distinct
    CD doublings stacked vertically.
  * At each level, there is a **binary binomial choice**:
    pick S-type (factor `N_S = 3`) or T-type (factor `N_T = 2`).
  * `(N_S + N_T)²⁵ = (3 + 2)²⁵ = 5²⁵` is the binomial expansion
    summing over all `2²⁵ = 33,554,432` partition choices.

So the 25 levels are 25 INDEPENDENT binomial-choice steps.
Within each step, the choice is binary {S or T} weighted (3, 2).

213-native: the (2+3)²⁵ formula is
**"choose S or T at each of 25 levels"**, NOT
"axis 2 and axis 3 stacked separately".
-/

namespace E213.Lib.Math.Geometry.GenerationRule.OrthogonalDirection

/-- ★ **25 binomial-choice steps**: total = `(N_S + N_T)^25`. -/
theorem binomial_orthogonal_direction :
    ((3 : Nat) + 2) ^ 25 = (5 : Nat) ^ 25 := rfl

/-- ★ **Number of partition choices** at each level: 2 (S or T). -/
theorem level_binary_choice : (2 : Nat) ^ 1 = 2 := rfl

/-- ★ **Total partitions over 25 levels**: `2²⁵ = 33,554,432`. -/
theorem total_partitions :
    (2 : Nat) ^ 25 = 33554432 := rfl

/-- ★ **Each partition contributes** `3^k · 2^(25-k)` for some
    `k ∈ {0, ..., 25}` (number of S-choices). -/
theorem partition_contribution_endpoints :
    (3 : Nat) ^ 0 * (2 : Nat) ^ 25 = 33554432
    ∧ (3 : Nat) ^ 25 * (2 : Nat) ^ 0 = 847288609443 :=
  ⟨rfl, rfl⟩

/-- ★ **Generation count from binomial**: `C(3, 2) = 3` matches
    `gen_count` in `Lib/Physics/Simplex/Counts.lean`. -/
theorem generation_count_match :
    E213.Lib.Math.Geometry.GenerationRule.GenerationCount.binom 3 2 = 3 := rfl

end E213.Lib.Math.Geometry.GenerationRule.OrthogonalDirection
