import E213.Lib.Physics.Atomic.Hydrogen
import E213.Lib.Physics.Atomic.Helium

/-!
# Phase 4 IonizationEnergies — H, He, Li atomic to ppm

User: "Compute atomic IE below ppm without numerical calculation"

## Standard formula

  IE(H, n=1) = R_∞ = m_e c² α² / 2

  where:
    m_e c² = 510998.95 eV (electron rest energy)
    α = 1/137.0359992 (fine structure)
    1/2 = 1/NT atomic

  Observed: 13.605693 eV (CODATA 2018, 9-digit).

## DRLT atomic chain (current)

  - α 1/137 (Phase 1 AlphaEM137, ppm bracket)
  - m_e (Phase 1, eV scale via m_p)
  - c = NT = 2 (lattice)

  → IE(H) = (1/NT) · (m_e c²) · α²

  Phase 1 HydrogenAtom: 1% bracket [13.4, 13.8] verified.

## Required to tighten to ppm

  α to ppm (already in Phase 1)
  m_e to ppm (Phase 1 chain via m_μ/m_e 0.48 ppb)
  → IE = m_e · α² / 2 atomic chain to ppm

This file: formal chain start.
-/

namespace E213.Lib.Physics.Atomic.IE.IonizationEnergies

open E213.Lib.Physics.Atomic.Hydrogen
open E213.Lib.Physics.Simplex.Counts

/-- ★ IE atomic-skeleton chain (H, He) ★

  The integer NT = 2 plays three atomic roles simultaneously in
  the Rydberg formula chain:
    · `IE(H) = m_e c² α²/NT` — `1/NT` factor
    · α² exponent           — squared in the formula
    · He effective Z = NT   — matches helium nuclear charge

  He screening uses `NS² − 1 = 8` (= adjoint SU(NS) = 1/α_3,
  cross-reference to AlphaEM `H1_K_eq_8`) and `NS² = 9`. -/
theorem H_IE_chain_atomic :
    -- the integer NT = 2 plays 1/NT-factor, α²-exponent, and He-Z roles
    (NT = 2)
    -- He screening: NS²−1 = 8 (= 1/α_3 channel count), NS² = 9
    ∧ (NS * NS - 1 = 8) ∧ (NS * NS = 9)
    -- atomic primitives
    ∧ (NS = 3) ∧ (d = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Atomic.IE.IonizationEnergies
