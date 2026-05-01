import E213.Physics.Simplex.Counts.Counts

/-!
# Information Library — information theory and quantum information atomic catalog

## Catalog

  Qubit dim = NT = 2
  Bell pair NT² = 4
  Bell quantum² = NT³ = 8
  Bekenstein 4 = d - 1
  No-cloning: Lens deterministic
-/

namespace E213.Physics.Library.InformationLibrary

open E213.Physics.Simplex.Counts

/-- Qubit = NT atomic. -/
theorem qubit : NT = 2 := by decide

/-- Bell pair NT² atomic. -/
theorem bell_pair : NT * NT = 4 := by decide

/-- Bell quantum² = NT³ = 8 atomic. -/
theorem bell_quantum : NT * NT * NT = 8 := by decide

end E213.Physics.Library.InformationLibrary
