import E213.Physics.Simplex.Counts.Counts

/-!
# Topology Library — topological invariant atomic catalog

## Δ⁴ topological invariants

  Euler char χ = 5 - 10 + 10 - 5 + 1 = 1
  K_{3,2}^(c=2) cycle dim b_1 = 8 = NS² - 1

## Z₂ topological invariant (TI)

  NT = 2 atomic = Z₂ atomic.

## Chern number

  Hall plateau ν atomic = NS = 3.
-/

namespace E213.Physics.Library.TopologyLibrary

open E213.Physics.Simplex.Counts

/-- Δ⁴ Euler characteristic = 1 (Nat arithmetic reorder: 16 - 15 = 1). -/
theorem euler_chi_1 : (5 + 10 + 1) - (10 + 5) = 1 := by decide

/-- K_{NS,NT}^(c) cycle space dim = NS² - 1 = 8. -/
theorem cycle_b_1 : NS * NS - 1 = 8 := by decide

/-- Z₂ TI invariant = NT = 2. -/
theorem z2_atomic : NT = 2 := by decide

end E213.Physics.Library.TopologyLibrary
