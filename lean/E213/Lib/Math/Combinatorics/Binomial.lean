import E213.Lib.Physics.Simplex.Counts

/-!
# Combinatorics — binomial coefficients (Pascal recursion)

Reuses `binom` from `Lib/Physics/Simplex/Counts.lean` (already
defined for the Δⁿ⁻¹ cohomology setup).  Extends with concrete
combinatorial identities and propEq witnesses.

Atomic content:
  * Pascal's recursion (already in `binom` definition by recursion).
  * Concrete C(n, k) values for small n.
  * Symmetry C(n, k) = C(n, n-k) (decide-checked).
  * Sum identity Σ_k C(n, k) = 2^n (decide-checked for small n).
-/

namespace E213.Lib.Math.Combinatorics.Binomial

open E213.Lib.Physics.Simplex.Counts (binom)

/-- C(0, 0) = 1 (rfl). -/
theorem binom_0_0 : binom 0 0 = 1 := rfl

/-- C(n, 0) = 1 for all n. -/
theorem binom_n_0 (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

/-- C(5, k) values forming Pascal's row 5: 1, 5, 10, 10, 5, 1. -/
theorem binom_5_table :
    binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
    ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1 := by decide

/-- C(4, k) values: 1, 4, 6, 4, 1. -/
theorem binom_4_table :
    binom 4 0 = 1 ∧ binom 4 1 = 4 ∧ binom 4 2 = 6
    ∧ binom 4 3 = 4 ∧ binom 4 4 = 1 := by decide

/-- ★ **Symmetry: C(n, k) = C(n, n-k)** ★ — atomic for small n. -/
theorem binom_5_symmetry :
    binom 5 0 = binom 5 5 ∧ binom 5 1 = binom 5 4
    ∧ binom 5 2 = binom 5 3 := by decide

/-- ★ **Row sum: Σ_k C(5, k) = 2^5 = 32** ★. -/
theorem binom_5_row_sum :
    binom 5 0 + binom 5 1 + binom 5 2 + binom 5 3 + binom 5 4 + binom 5 5
    = 32 := by decide

/-- Row sum: Σ_k C(4, k) = 2^4 = 16. -/
theorem binom_4_row_sum :
    binom 4 0 + binom 4 1 + binom 4 2 + binom 4 3 + binom 4 4 = 16 :=
  by decide

/-- Atomic Pascal step at (5, 2): C(5, 2) = C(4, 1) + C(4, 2) = 4 + 6 = 10. -/
theorem pascal_5_2 : binom 5 2 = binom 4 1 + binom 4 2 := by decide

/-- Vanishing for k > n: C(5, 6) = 0 (Grade-overflow, matches
    cohomology dimensional bound). -/
theorem binom_5_6_zero : binom 5 6 = 0 := by decide

/-- Vanishing for k > n: C(4, 5) = 0. -/
theorem binom_4_5_zero : binom 4 5 = 0 := by decide

end E213.Lib.Math.Combinatorics.Binomial
