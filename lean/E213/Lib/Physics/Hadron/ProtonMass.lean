import E213.Lib.Physics.Higgs.Mass

/-!
# m_p — closed propagator narrative + proton atomic structure (0 axioms)

DRLT narrative formula (numerical, not Lean-computed):

  m_p = NS · Λ_QCD · P(α_GUT · NS / d)

  where P(x) = (1 + 2x)/(1 + x)  (closed Dyson resummation)

## Numerical narrative (informal)

  NS · Λ_QCD   = 3 · 308.32 = 924.97 MeV   [combinatorial 3-quark]
  x = α_GUT · NS / d = 0.0243 · 3/5 = 0.01459
  P(x) = (1 + 0.02918)/(1 + 0.01459) = 1.01438
  m_p = 924.97 · 1.01438 ≈ 938 MeV

  This is a narrative breakdown; the Lean theorem below proves only
  the genuine *integer atomic readings* (NT² = 4, d−1 = 4, d³ = 125,
  the NS/d = 3/5 closed-propagator argument scale).  m_p itself is
  not derived as a Lean theorem here.

## ★ Closed propagator P(x) — universal Dyson form ★

  P(x) = (1 + 2x)/(1 + x) is **exact**, not series approximation.
  UV-finite by construction (continuum QFT requires renormalization,
  here fraction closes itself).

  Same P(x) appears in:
  - m_μ/m_e Dyson series (geometric)
  - m_p (this file)
  - general fermion mass (closed propagator)

## ★ Atomic ratio NS/d = 3/5 ★

  Argument of P is α_GUT · (NS/d) — same Y-norm-style factor 5/3
  inverse appearing!  At GUT scale: x = α_GUT · NS/d.

  → The same d/NS atomicity appears again.
-/

namespace E213.Lib.Physics.Hadron.ProtonMass

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.AlphaEM.Prefactors

/-- Closed propagator argument: x = α_GUT · NS / d.
    NS/d = 3/5 = atomic ratio (inverse of Y-norm 5/3). -/
def closed_prop_factor_num : Nat := NS  -- = 3
def closed_prop_factor_den : Nat := d   -- = 5

/-- Closed propagator structure P(x) = (1+2x)/(1+x).
    Same form as α_em IR's Dyson tail expansion, but written as
    closed fraction (Dyson resummed). -/
def closed_prop_num_factor : Nat := 2  -- "1 + 2x" numerator
def closed_prop_den_factor : Nat := 1  -- "1 + x" (1·x) denominator

/-- Proton atomic structure readings (integer arithmetic only).

  The narrative closed-propagator form m_p = NS · Λ_QCD · (1+2x)/(1+x)
  with x = α_GUT · NS / d is informal (see module docstring); m_p
  is **not** derived as a Lean theorem.  What is proven here are the
  genuine integer atomic readings:

    · NS = 3 valence quarks, d = 5 dimension
    · NS/d = 3/5 atomic ratio (inverse Y-norm); cross-mult 5·3 = 3·5
    · Closed propagator (1+2x)/(1+x) atomic factors (2, 1)
    · Proton charge radius r_p · m_p / (ℏc) = NT² = 4 with three
      atomic readings (NT² = d−1 = NS+1)
    · α_GUT/d³ leak coefficient d³ = 125 (3D spatial simplex volume). -/
theorem proton_atomic_readings :
    -- Atomic primitives
    NS = 3 ∧ NT = 2 ∧ d = 5
    -- NS/d = 3/5 atomic ratio (closed propagator argument scale)
    ∧ closed_prop_factor_num = 3
    ∧ closed_prop_factor_den = 5
    -- Cross-mult: 5·3 = 3·5 (inverse-Y-norm)
    ∧ closed_prop_factor_den * 3 = closed_prop_factor_num * 5
    -- Closed propagator P(x) atomic factors
    ∧ closed_prop_num_factor = 2
    ∧ closed_prop_den_factor = 1
    -- r_p · m_p / (ℏc) = NT² = 4 (three atomic readings)
    ∧ NT * NT = 4
    ∧ d - 1 = 4
    ∧ NS + 1 = 4
    -- α_GUT/d³ leak coefficient = 125 = 3D volume
    ∧ d ^ 3 = 125 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  <;> decide

end E213.Lib.Physics.Hadron.ProtonMass
