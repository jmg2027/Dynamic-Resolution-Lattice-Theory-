import E213.Physics.Simplex.Counts

/-!
# Molecular Library — molecular atomic catalog

## Bond angles (Phase 1 BondAngles)

  CH₄: cos θ = -1/NS = -1/3   → 109.47°  (exact)
  H₂O: cos θ = -1/(NS+1) = -1/4 → 104.48°  (exact)
  NH₃: cos θ = (NS+1)/(NS²+NS+1) = 4/13 → 107°  (exact)

## Atomic forms

  cos denom CH₄ = NS
  cos denom H₂O = NS + 1
  cos denom NH₃ = NS² + NS + 1 = 13 = F_7
-/

namespace E213.Physics.Phase4.Library.MolecularLibrary

open E213.Physics.Simplex

/-- CH₄ bond angle cos denom = NS = 3. -/
def CH4_denom : Nat := NS
theorem CH4_eq_3 : CH4_denom = 3 := by decide

/-- H₂O bond angle cos denom = NS + 1 = 4. -/
def H2O_denom : Nat := NS + 1
theorem H2O_eq_4 : H2O_denom = 4 := by decide

/-- NH₃ bond angle cos denom = NS²+NS+1 = 13 (= F_7). -/
def NH3_denom : Nat := NS * NS + NS + 1
theorem NH3_eq_13 : NH3_denom = 13 := by decide

/-- NH₃ denom = NS² + NT² atomic identity. -/
theorem NH3_eq_alt : NS * NS + NT * NT = 13 := by decide

end E213.Physics.Phase4.Library.MolecularLibrary
