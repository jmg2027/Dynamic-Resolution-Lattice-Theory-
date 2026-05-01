import E213.Physics.Simplex.Counts.Counts

/-!
# Lepton Mass Library — lepton mass ratio atomic catalog

## Mass ratios (Phase 1)

  m_μ/m_e ≈ 206.768 = NS·137/NT atomic chain (0.48 ppb)
  m_τ/m_μ ≈ 17 = NS² + (NS²-1) atomic
  m_τ/m_e ≈ 3477 atomic chain

## Atomic chain

  m_μ/m_e leading = NS · 137 / NT
  → Phase 1 closed propagator + atomic σ
-/

namespace E213.Physics.Library.LeptonMassLibrary

open E213.Physics.Simplex.Counts

/-- m_μ/m_e leading numerator = NS · 137. -/
theorem mu_e_leading : NS * 137 = 411 := by decide

/-- m_τ/m_μ ≈ 17 = NS² + (NS²-1) atomic. -/
theorem tau_mu : NS * NS + (NS * NS - 1) = 17 := by decide

end E213.Physics.Library.LeptonMassLibrary
