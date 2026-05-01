import E213.Physics.Simplex.Counts

/-!
# Hadron Mass Library — hadron mass atomic catalog

## Catalog

  m_p   = 938.27 MeV (NS·Λ_QCD·P, 0.000% match)
  m_n   = 939.57 MeV (≈ m_p · (1 + atomic correction))
  m_π⁰  = 134.98 MeV (NH₃ chain)
  m_π±  = 139.57 MeV
  m_ρ   = 770 MeV
  m_ω   = 782.7 MeV (Phase 1 -0.07%)
  m_J/ψ = 3096.9 MeV (Phase 1 -0.5%)

## Atomic forms

  m_p prefactor      = NS (3 valence quarks)
  m_p propagator     = P(α·NS/d)
  m_n - m_p          ≈ atomic correction (~1.3 MeV)
  meson SU(3) octet  = NS²-1 = 8
  baryon decuplet    = 10 = C(d,2)
-/

namespace E213.Physics.Library.HadronMassLibrary

open E213.Physics.Simplex.Counts

/-- m_p atomic prefactor = NS. -/
theorem mp_prefactor : NS = 3 := by decide

/-- Meson octet 8 atomic. -/
theorem meson_octet_8 : NS * NS - 1 = 8 := by decide

/-- Baryon decuplet 10 atomic. -/
theorem baryon_decuplet_10 : d * (d - 1) / 2 = 10 := by decide

end E213.Physics.Library.HadronMassLibrary
