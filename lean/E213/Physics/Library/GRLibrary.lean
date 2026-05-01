import E213.Physics.Simplex.Counts.Counts

/-!
# GR Library — gravity and general relativity atomic catalog

## Catalog

  Spacetime (3+1) = (NS, NT) atomic
  c (speed of light) = NT = 2 atomic
  Minkowski signature: NS² - NT² = 5 = d
  Einstein 8π factor: 8 = NS² - 1 atomic
  Hawking 1/8 = 1/(NS²-1) atomic
  Schwarzschild factor 2 = NT atomic
  No-hair: 3 = NS atomic
  G_N normalization: 1/d = 1/5
-/

namespace E213.Physics.Library.GRLibrary

open E213.Physics.Simplex.Counts

/-- c = NT lattice speed. -/
theorem c_atomic : NT = 2 := by decide

/-- Minkowski signature NS² - NT² = d. -/
theorem minkowski_sig : NS * NS - NT * NT = d := by decide

/-- Einstein 8π factor = NS² - 1 atomic. -/
theorem einstein_8 : NS * NS - 1 = 8 := by decide

/-- Schwarzschild 2 = NT atomic. -/
theorem schwarzschild_2 : NT = 2 := by decide

/-- No-hair 3 parameter = NS atomic. -/
theorem no_hair : NS = 3 := by decide

end E213.Physics.Library.GRLibrary
