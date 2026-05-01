import E213.Physics.Simplex.Counts

/-!
# PMNS Library — Neutrino mixing atomic catalog

## Catalog

  sin²θ₁₂ leading = 1/NS = 1/3
  sin²θ₂₃ leading = 1/NT = 1/2
  sin²θ₁₃ leading = α_GUT
  δ_CP            = 180 + 360/(d²-1) = 195°
  m₃/m₂           ≈ 5.71 (Phase 3 derivation, +0.04%)

## Atomic integers

  θ₁₂ denom = NS
  θ₂₃ denom = NT
  δ_CP denom = d²-1 = 24 (adjoint SU(d))
-/

namespace E213.Physics.Library.PMNSLibrary

open E213.Physics.Simplex.Counts

/-- sin²θ₁₂ denom = NS. -/
def theta_12_denom : Nat := NS
theorem theta_12_eq_3 : theta_12_denom = 3 := by decide

/-- sin²θ₂₃ denom = NT. -/
def theta_23_denom : Nat := NT
theorem theta_23_eq_2 : theta_23_denom = 2 := by decide

/-- δ_CP denom = d²-1 = 24 (adjoint SU(5)). -/
def delta_cp_denom : Nat := d * d - 1
theorem delta_cp_eq_24 : delta_cp_denom = 24 := by decide

/-- δ_CP value = 195° atomic. -/
theorem delta_cp_value : 180 + 360 / 24 = 195 := by decide

end E213.Physics.Library.PMNSLibrary
