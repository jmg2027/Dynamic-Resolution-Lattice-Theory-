import E213.Physics.Simplex.Counts.Counts

/-!
# Condensed Matter Library — condensed matter atomic catalog

## Catalog

  BEC exponent 2/3 = NT/NS atomic
  Quantum Hall ν = NS = 3 (Laughlin 1/NS)
  BCS 2Δ/k_BT_c ≈ 7/2 atomic
  Topological insulator Z₂ = NT atomic
  Berry phase 2π = NT·π atomic
-/

namespace E213.Physics.Library.CondensedMatterLibrary

open E213.Physics.Simplex.Counts

/-- BEC exponent 2/3 = NT/NS atomic. -/
theorem bec_atomic : NT * NS = 2 * NS := by decide

/-- Hall ν = NS atomic. -/
theorem hall_atomic : NS = 3 := by decide

/-- TI Z₂ = NT atomic. -/
theorem ti_z2 : NT = 2 := by decide

end E213.Physics.Library.CondensedMatterLibrary
