import E213.Physics.AlphaEM.UnifiedSum
import E213.Physics.Cosmology.NeffDerivation

/-!
# 1/α_em(IR) — Lens-level derivation attempt for five terms (0 axioms part)

Continuing user directive (2026-04-27): "derive as a single lattice sum".
This file makes explicit that each of the five terms comes from prior Lean theorems,
and formalizes the open question of *why exactly these five terms*.

## Five-term decomposition

  1/α_em(IR) = 1/α_3 + 1/α_2 + (5/3)·(1/α_1) + 1/NS + α_GUT/(NS+1)

Prior source for each term:
  Term 1: 1/α_3 = NS² - 1 = 8
          ← `SimplexCounts.inv_alpha_3_confined`
          ← `NeffDerivation.alpha_3_Neff_eq_1` (rank exhaustion at NS²)
  Term 2: 1/α_2 = 12·NT·S(NT) = 30
          ← `AlphaEM.inv_alpha_2_eq_30`
          ← `NeffDerivation.alpha_2_Neff_eq_2` (rank exhaustion at NT)
  Term 3: (5/3)·(1/α_1) = 60·ζ(2) = 10π²
          ← `AlphaEM.inv_alpha_1_lower/upper`
          ← `WhyBasel.basel_structurally_forced` (1/n² from NS=3)
          ← Y-normalisation factor 5/3 (SU(5) embedding)
  Term 4: 1/NS = 1/3
          ← trivially from NS = 3
          ← also = NT/(d+1) = 2/6  ★ d+1 cofactor pattern
  Term 5: α_GUT/(NS+1) = α_GUT/4
          ← `AlphaGUT` (α_GUT bracket)
          ← also = α_GUT/(d-1)  ★ d-1 cofactor pattern

## ★ Key structural hint — d±1 cofactor symmetry ★

  d² - 1 = (d-1)(d+1) = 4·6 = 24 = adjoint SU(5)
  1/NS                 = NT/(d+1)
  α_GUT/(NS+1)         = α_GUT/(d-1)

This may be more than a simple arithmetic coincidence — the hypothesis that
the d² = (d-1)(d+1) + 1 factorisation directly points to the lattice cofactors.

## Open question

  ◯ Strict Lens-level derivation of *why exactly this sum* for the five terms:
    - Lean definition of photon-as-cross-sector-U(1)
    - Summation mechanism for each sector's contribution
    - Lens origin of the d±1 cofactor decomposition
  Currently only established: "each term is a prior quantity" and "sum is ppm match".
-/

namespace E213.Physics.AlphaEM.FiveTermDerivation

open E213.Physics.Simplex.Counts

/-- Term 4 alternative form: 1/NS = NT/(d+1).
    Cross-mult: NS·NT = d+1 = 6 ✓ (since 3·2=6, NS+NT+1=6). -/
theorem inv_NS_eq_NT_over_d_plus_1 :
    NT * NS = d + 1 := by decide

/-- Term 5 denominator: NS+1 = d-1 = 4. -/
theorem NS_plus_1_eq_d_minus_1 :
    NS + 1 = d - 1 := by decide

/-- d² - 1 = (d-1)(d+1) = 24 — adjoint SU(5). -/
theorem d_sq_minus_1_factorises :
    d * d - 1 = (d - 1) * (d + 1)
    ∧ (d - 1) * (d + 1) = 24 := by decide

/-- d² = (d-1)(d+1) + 1 — Pell-style identity. -/
theorem d_sq_pell_form :
    d * d = (d - 1) * (d + 1) + 1 := by decide

/-- ★ Cofactor decomposition master theorem ★
    All five terms align with the *factorisation pattern* of d, NS, NT.

    d² - 1 = (d-1)(d+1) = adjoint SU(5)
    1/NS   = NT/(d+1)   ← d+1 cofactor
    α_GUT/(NS+1) = α_GUT/(d-1)   ← d-1 cofactor

    The hypothesis that the Pell-form factorisation of d² splits the lattice cofactors
    into two branches, with each cofactor corresponding to one of the five terms. -/
theorem cofactor_pattern :
    -- d² - 1 = (d-1)(d+1)
    (d * d - 1 = (d - 1) * (d + 1))
    -- d+1 cofactor in 1/NS
    ∧ (NT * NS = d + 1)
    -- d-1 cofactor in α_GUT-tail
    ∧ (NS + 1 = d - 1)
    -- Concrete values
    ∧ (d - 1 = 4) ∧ (d + 1 = 6) := by decide

/-- Each of the five terms matches a prior theorem quantity — citation theorem. -/
theorem five_terms_traceable :
    -- Term 1: 1/α_3 = 8 (NS² - 1)
    (NS * NS - 1 = 8)
    -- Term 2: 1/α_2 = 30 (12·NT·5/4)
    ∧ (12 * NT * 5 / 4 = 30)
    -- Term 4: 1/NS = NT/(d+1) (alternative form)
    ∧ (NT * NS = d + 1)
    -- Term 5: NS+1 = d-1 (cofactor)
    ∧ (NS + 1 = d - 1)
    -- d²-1 = (d-1)(d+1) = adjoint
    ∧ (d * d - 1 = (d - 1) * (d + 1)) := by decide

/-- **Open**: Lens-level derivation of *why exactly this sum* for the five terms.
    Currently established: numerical match (ppm) + structural traceability + d±1
    cofactor pattern.  The strict derivation chain of
    Photon = cross-sector U(1) phase, Raw + Lens definition, IR coupling = summation mechanism = five terms
    is separate work.  -/
theorem derivation_open : True := trivial

end E213.Physics.AlphaEM.FiveTermDerivation
