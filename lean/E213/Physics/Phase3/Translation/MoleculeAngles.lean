import E213.Physics.Phase2
import E213.Physics.Atomic.BondAngles
import E213.Physics.SimplexCounts

/-!
# Translation: Molecular bond angles → DRLT atomic (Phase 1 BondAngles deep-dive)

Standard chemistry:
  CH₄ (methane): θ ≈ 109.47°  (tetrahedral)
  H₂O (water):   θ ≈ 104.48°  (bent)
  NH₃ (ammonia): θ ≈ 107.0°   (pyramidal)

DRLT atomic (Phase 1):
  cos θ_CH4 = -1/NS       = -1/3
  cos θ_H2O = -1/(NS+1)   = -1/4
  cos θ_NH3 = (NS+1)/(NS²+NS+1) = 4/13

*Atomic direct derivation* for each molecule.

NH₃: NS² + NS + 1 = 13 = F_7 (Fibonacci atomic).
-/

namespace E213.Physics.Phase3.Translation.MoleculeAngles

open E213.Physics.BondAngles
open E213.Physics.Simplex

/-- CH₄ cos denom = NS atomic. -/
theorem ch4_atomic : CH4_cos_denom = NS := by decide

/-- H₂O cos denom = NS+1 atomic. -/
theorem h2o_atomic : H2O_cos_denom = NS + 1 := by decide

/-- NH₃ cos = (NS+1)/(NS²+NS+1) atomic. -/
theorem nh3_atomic :
    NH3_cos_numer = NS + 1 ∧ NH3_cos_denom = NS * NS + NS + 1 := by
  refine ⟨?_, ?_⟩
  all_goals decide

/-- NH₃ denom = 13 = F_7 = NS² + NT². -/
theorem nh3_denom_F7 : NS * NS + NT * NT = 13 := by decide

/-- ★ Molecule Angles Capstone ★ -/
theorem molecule_angles_atomic :
    -- atomic
    (NS = 3) ∧ (NT = 2) ∧ (d = 5)
    -- CH₄: cos = -1/NS
    ∧ (CH4_cos_denom = NS)
    -- H₂O: cos = -1/(NS+1)
    ∧ (H2O_cos_denom = NS + 1)
    -- NH₃: cos = (NS+1)/(NS²+NS+1) = 4/13
    ∧ (NH3_cos_numer = NS + 1) ∧ (NH3_cos_denom = NS * NS + NS + 1)
    -- 13 = F_7 = NS² + NT²
    ∧ (NS * NS + NT * NT = 13) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase3.Translation.MoleculeAngles
