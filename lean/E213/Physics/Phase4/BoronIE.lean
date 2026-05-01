import E213.Physics.Simplex.Counts

/-!
# Phase 4 BoronIE — B IE atomic chain + P(x)

## DRLT chain

  Z = d = 5
  σ_1s_to_2p = 7/8 (Phase 1)
  σ_2s_to_2p = 17/20 = (NS² + NS²-1)/(4d) atomic
  σ_total = 2·7/8 + 2·17/20 = 35/20 + 34/20 = 69/20
  Z_eff = 5 - 69/20 = 31/20
  Z_eff² = 961/400
  n² = NT² = 4

  Leading IE(B) = R · 961/(400·4) = R · 961/1600

## Numerical

  R · 961/1600 = 13605693 · 961/1600 = 8171919 μeV
  observed = 8298019 μeV
  diff = 126100 μeV = 1.52%

  + P(x) (closed propagator):
    P(0.01458) = 1.01437
    8171919 · 1.01437 = 8289344
    diff = 8675 μeV = **1046 ppm** ★

  → 1.52% → 1046 ppm improvement.

Additional σ_2s_to_2p atomic refinement needed to reach ppm.
-/

namespace E213.Physics.Phase4.BoronIE

open E213.Physics.Simplex

/-- B leading IE (no propagator) = R · 961/1600 μeV. -/
def B_leading : Nat := 8171919

/-- B with P(x) correction. -/
def B_with_P_x : Nat := 8289344

/-- B observed. -/
def B_observed : Nat := 8298019

/-- B precision with P(x): 1046 ppm. -/
theorem B_with_P_x_diff :
    B_observed - B_with_P_x = 8675 := by decide

/-- σ_2s_to_2p atomic: 17/(4·d) = 17/20.  17 = NS² + (NS²-1). -/
theorem sigma_atomic : NS * NS + (NS * NS - 1) = 17 := by decide

end E213.Physics.Phase4.BoronIE
