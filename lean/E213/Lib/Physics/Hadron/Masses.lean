import E213.Lib.Physics.Hadron.ProtonMass

/-!
# Hadron masses — GMOR + hyperfine lattice form (0 axioms part)

DRLT formulae:

  GMOR (pseudoscalar):
    m_PS² = NS² · (m_q1 + m_q2) · Λ_QCD     [n_eff = NS² = 9]

  Vector meson (hyperfine):
    m_ρ² = m_π² + Δ²
    Δ = d · Λ_QCD / NT  [hyperfine splitting]

## Key lattice atoms

  GMOR n_eff = NS² = 9
    → same NS² primitive (paired with 1/α_3 = NS²-1)

  Hyperfine Δ = d·Λ/NT
    → d/NT ratio (variant of d/NS)

## Numerical narrative (informal, off-Lean)

  m_π:  DRLT 137.6 MeV vs PDG 137.3 MeV
  m_ρ:  DRLT 782.1 MeV vs PDG 782.7 MeV
  m_ω:  DRLT 782.1 MeV (= m_ρ)
  m_J/ψ: DRLT 3081.6 MeV vs PDG 3096.9 MeV
  Δ-N split: DRLT 295.7 MeV vs 294 MeV

  These DRLT-vs-PDG figures are informal off-Lean estimates; the Lean
  theorem proves only the genuine atomic-integer identities.

## Same atomicity-locked pattern

  - NS² = 9 prefactor (GMOR n_eff)
  - d/NT = 5/2 (hyperfine ratio)
  - Λ_QCD scale (derived from QCD-scale chain)
  - Closed propagator P(x) for heavy quarks
-/

namespace E213.Lib.Physics.Hadron.Masses

open E213.Lib.Physics.Simplex.Counts

/-- GMOR n_eff = NS² = 9.  Prefactor in the m_π² formula.
    Externally consumed by `Hadron/Bridge` and `Capstones/PhysicsTrackComplete`. -/
def gmor_n_eff : Nat := NS * NS

/-- Hyperfine factor: d / NT = 5/2. -/
def hyperfine_num : Nat := d
def hyperfine_den : Nat := NT

/-- Atomicity-locked hadron pattern: GMOR + hyperfine atomic
    integer readings (no precision claim).

    Bundles:
      · GMOR n_eff = NS² = 9; adjoint identity NS² = (NS²−1) + 1
      · Hyperfine factor d/NT = 5/2 (cross-mult), atomic table
      · Hyperfine × Proton-factor cross identities
        (d/NT)·(NS/d) = NS/NT = 3/2 (m_μ/m_e ratio)
      · Atomic primitives -/
theorem hadron_simplicial_pattern :
    -- GMOR n_eff = NS² = 9
    gmor_n_eff = 9
    ∧ gmor_n_eff = (NS * NS - 1) + 1
    ∧ NS * NS - 1 = 8                                   -- = 1/α_3
    -- Hyperfine atomic
    ∧ hyperfine_num = d ∧ hyperfine_den = NT
    ∧ hyperfine_num = 5 ∧ hyperfine_den = 2
    -- Hyperfine vs Proton factor cross identities
    ∧ hyperfine_num * 2 = hyperfine_den * 5             -- d·2 = NT·5
    ∧ NS * 5 = d * 3                                    -- NS/d = 3/5
    ∧ NS * 2 = NT * 3                                   -- = m_μ/m_e
    -- Atomic primitives
    ∧ NS = 3 ∧ NT = 2 ∧ d = 5 := by decide

end E213.Lib.Physics.Hadron.Masses
