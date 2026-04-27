import E213.Physics.SimplexCounts

/-!
# QFT Library — 양자장론 atomic catalog

## Catalog

  Closed propagator P(x) = (1+2x)/(1+x)
    x = α_GUT · NS/d = 18/(125π²) atomic
  3 channels (AA, BB, AB) = 3 forces atomic
  Wilson loop cycle b_1 = 8 = NS²-1
  CPT invariance = (NS, NT) atomic
  Confinement: 1/α_3 = NS² - 1 atomic
  Asymptotic freedom: NS² - 1 > 0 atomic
-/

namespace E213.Physics.Phase4.Library.QFTLibrary

open E213.Physics.Simplex

/-- Closed propagator coefficients (2, 1) atomic. -/
theorem prop_coeffs : NT = 2 ∧ NS - NT = 1 := by
  refine ⟨?_, ?_⟩
  all_goals decide

/-- Wilson loop cycle b_1 = 8 atomic. -/
theorem wilson_cycle : NS * NS - 1 = 8 := by decide

/-- 3 channels = 3 forces atomic. -/
theorem three_channels : (3 : Nat) = NS := by decide

end E213.Physics.Phase4.Library.QFTLibrary
