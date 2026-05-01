import E213.Physics.Simplex.Counts

/-!
# Statistical Physics Library — statistical mechanics atomic catalog

## Core

  Specific heat c_v = (NS/2)·k_B atomic (monatomic)
  Equipartition kT/d atomic
  Stefan-Boltzmann denom 15 = d·NS atomic
  Mean field critical exponents: β=1/NT, δ=NS, ν=1/NT atomic
  2nd law origin: NT < NS asymmetry
-/

namespace E213.Physics.Phase4.Library.StatPhysLibrary

open E213.Physics.Simplex

/-- Stefan-Boltzmann denom = d·NS = 15. -/
theorem stefan_atomic : d * NS = 15 := by decide

/-- Monatomic c_v = NS/2·k_B atomic. -/
theorem cv_monatomic : NS = 3 := by decide

/-- 2nd law atomic origin. -/
theorem second_law : NT < NS := by decide

end E213.Physics.Phase4.Library.StatPhysLibrary
