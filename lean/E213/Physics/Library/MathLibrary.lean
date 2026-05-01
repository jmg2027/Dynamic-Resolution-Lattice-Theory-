import E213.Physics.Simplex.Counts

/-!
# Math Library — mathematics atomic catalog

No standard mathematics borrowing.  Atomic integers only.

## Primes atomic

  2 = NT, 3 = NS, 5 = d, 7 = NS²-NT,
  13 = NS²+NT², 41 = α_GUT integer, 137 = 1/α_em

## Fibonacci atomic (Phase 1 FibonacciAtomic)

  F_3 = NT, F_4 = NS, F_5 = d,
  F_6 = NS²-1 = 8, F_7 = NS²+NT² = 13

## Combinatorics atomic

  C(d, 0) = 1, C(d, 1) = d, C(d, 2) = 10, C(d, 3) = 10
  C(d, 4) = d, C(d, 5) = 1
  3! = 6, 4! = 24, 5! = 120

## Polytope atomic

  5-simplex Δ⁴ vertex = d
  edges = C(d, 2) = 10
  2-faces = C(d, 3) = 10
  3-faces = C(d, 4) = d
  4-cell = 1

## Group theory atomic

  SU(NT) generators = NT² - 1 = 3
  SU(NS) generators = NS² - 1 = 8
  SU(d) generators = d² - 1 = 24
  Cartan rank SU(NS) = NS - 1 = NT
  SU(NS) roots = NS·(NS-1) = 6 = NS·NT
-/

namespace E213.Physics.Library.MathLibrary

open E213.Physics.Simplex.Counts

/-- Atomic primes catalog. -/
theorem primes_catalog :
    (NT = 2) ∧ (NS = 3) ∧ (d = 5)
    ∧ (NS * NS - NT = 7)
    ∧ (NS * NS + NT * NT = 13) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- Combinatorics on d=5. -/
theorem combinatorics_atomic :
    (3 * 2 * 1 = 6)
    ∧ (4 * 3 * 2 * 1 = 24)
    ∧ (NS * NT = 6)
    ∧ (d * d - 1 = 24) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals decide

/-- Group theory atomic. -/
theorem group_atomic :
    (NS * NS - 1 = 8)
    ∧ (NT * NT - 1 = 3)
    ∧ (d * d - 1 = 24)
    ∧ (NS - 1 = NT)
    ∧ (NS * (NS - 1) = NS * NT) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Library.MathLibrary
