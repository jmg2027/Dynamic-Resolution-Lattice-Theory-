import E213.Physics.Simplex.Counts

/-!
# Phase 4 Material Catalog — atomic identities for masses + couplings

Consolidates AtomicMass, Coupling, Hadron mass, Lepton mass,
Molecular catalog files into a single Material.lean.
-/

-- ============================================================
-- AtomicMassLibrary
-- ============================================================
namespace E213.Physics.Phase4.Library.AtomicMassLibrary

open E213.Physics.Simplex

/-- m_p 4-digit (in 10⁻⁴ amu) = 10078 (= 1.0078). -/
def m_p_4digit : Nat := 10078

/-- m(He)/m(H) atomic ≈ NT² = 4. -/
theorem mass_ratio_He_H_atomic : NT * NT = 4 := by decide

/-- m(O)/m(C) atomic ≈ ?  16/12 = 4/3 = NS+1/NS atomic. -/
theorem mass_ratio_O_C_atomic : (4 : Nat) * NS = (NS + 1) * NS := by decide

end E213.Physics.Phase4.Library.AtomicMassLibrary

-- ============================================================
-- CouplingLibrary
-- ============================================================
namespace E213.Physics.Phase4.Library.CouplingLibrary

open E213.Physics.Simplex

/-- 1/α_3 = 8 atomic. -/
def inv_alpha_3 : Nat := NS * NS - 1

theorem inv_alpha_3_eq_8 : inv_alpha_3 = 8 := by decide

/-- 1/α_2 = 30 atomic = NS·NT·d. -/
def inv_alpha_2 : Nat := NS * NT * d

theorem inv_alpha_2_eq_30 : inv_alpha_2 = 30 := by decide

/-- α_GUT denom = d² · π² → atomic d² = 25. -/
def alpha_gut_denom_int : Nat := d * d

theorem alpha_gut_denom_eq_25 : alpha_gut_denom_int = 25 := by decide

/-- 1/α_em ≈ 137 (Phase 1 ppm). -/
def inv_alpha_em_int : Nat := 137

end E213.Physics.Phase4.Library.CouplingLibrary

-- ============================================================
-- HadronMassLibrary
-- ============================================================
namespace E213.Physics.Phase4.Library.HadronMassLibrary

open E213.Physics.Simplex

/-- m_p atomic prefactor = NS. -/
theorem mp_prefactor : NS = 3 := by decide

/-- Meson octet 8 atomic. -/
theorem meson_octet_8 : NS * NS - 1 = 8 := by decide

/-- Baryon decuplet 10 atomic. -/
theorem baryon_decuplet_10 : d * (d - 1) / 2 = 10 := by decide

end E213.Physics.Phase4.Library.HadronMassLibrary

-- ============================================================
-- LeptonMassLibrary
-- ============================================================
namespace E213.Physics.Phase4.Library.LeptonMassLibrary

open E213.Physics.Simplex

/-- m_μ/m_e leading numerator = NS · 137. -/
theorem mu_e_leading : NS * 137 = 411 := by decide

/-- m_τ/m_μ ≈ 17 = NS² + (NS²-1) atomic. -/
theorem tau_mu : NS * NS + (NS * NS - 1) = 17 := by decide

end E213.Physics.Phase4.Library.LeptonMassLibrary

-- ============================================================
-- MolecularLibrary
-- ============================================================
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

