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

/-- ★ Pascal's row 5: 1, 5, 10, 10, 5, 1 — the d=5 simplex
    grade dimensions for K_{3,2}^{(c=2)} ↪ Δ⁴.  Symmetric:
    C(5, k) = C(5, 5−k).  Row sum 2⁵ = 32. -/
theorem binom_5_row :
    binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
    ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1
    ∧ binom 5 0 + binom 5 1 + binom 5 2
        + binom 5 3 + binom 5 4 + binom 5 5 = 32
    ∧ binom 5 6 = 0  -- vanishes above grade d
    := by decide

/-- ★ Atomic Pascal step at (5, 2): C(5, 2) = C(4, 1) + C(4, 2)
    = 4 + 6 = 10.  The single non-trivial recursion call needed
    in the d=5 simplex; row 4 enters only via this step. -/
theorem pascal_5_2 : binom 5 2 = binom 4 1 + binom 4 2 := by decide

end E213.Lib.Math.Combinatorics.Binomial
