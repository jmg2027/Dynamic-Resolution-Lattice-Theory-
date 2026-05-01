import E213.Physics.Simplex.Counts

/-!
# Optics Library — optics atomic catalog

## Catalog

  Stefan-Boltzmann denom 15 = d·NS atomic
  Brewster ratio = NS/NT = 3/2 atomic
  Maxwell 4 equations = d - 1 atomic
  Optical theorem 4π = (d-1)·π
-/

namespace E213.Physics.Phase4.Library.OpticsLibrary

open E213.Physics.Simplex

/-- Stefan denom = 15 atomic. -/
theorem stefan_atomic : d * NS = 15 := by decide

/-- Brewster ratio NS/NT atomic. -/
theorem brewster : NS * 2 = 3 * NT := by decide

/-- Maxwell 4 equations atomic. -/
theorem maxwell_4 : d - 1 = 4 := by decide

end E213.Physics.Phase4.Library.OpticsLibrary
