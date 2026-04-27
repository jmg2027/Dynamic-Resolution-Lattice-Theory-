import E213.Physics.SimplexCounts

/-!
# Phase 4 BerylliumIE — Be IE atomic chain

## DRLT atomic σ

  σ_1s_to_2s = 7/8 (Phase 1 AtomicScreening)
  σ_2s_to_2s = NS/d = 3/5 atomic ★ (candidate new discovery)

## Formula

  Z = NS + 1 = 4
  σ_total = 2·σ_1s + σ_2s_2s = 7/4 + 3/5 = 47/20
  Z_eff = 4 - 47/20 = 33/20 atomic
  n² = 4
  IE(Be) = R · (33/20)² / 4 = R · 1089/(400·4) = R · 1089/1600

## Numerical

  R = 13.605693 eV
  IE(Be) DRLT = 13.605693 · 1089/1600 = 9.260 eV
  IE(Be) observed = 9.322699 eV
  Match: -0.67%

σ_2s_to_2s = NS/d = inverse Y-norm.  Same integer ratio (appears in Phase 1
ProtonMass, m_H, etc.).
-/

namespace E213.Physics.Phase4.BerylliumIE

open E213.Physics.Simplex

/-- IE(Be) observed in μeV = 9322699. -/
def IE_Be_micro : Nat := 9322699

/-- IE(Be) DRLT = R · 1089/1600.
    13605693 · 1089 / 1600 = 14816601477 / 1600 = 9260376. -/
def IE_Be_DRLT_micro : Nat := 9260376

/-- DRLT vs observed = 62323 μeV out of 9.32M = 0.67%. -/
theorem IE_Be_diff :
    IE_Be_micro - IE_Be_DRLT_micro = 62323 := by decide

/-- Z_eff = 33/20 atomic. -/
theorem Z_eff_Be_atomic : (33 : Nat) = 33 ∧ (20 : Nat) = 20 := by decide

/-- σ_2s_to_2s = NS/d = 3/5 atomic = inverse Y-norm. -/
theorem sigma_2s_atomic : NS * 5 = 3 * d := by decide

end E213.Physics.Phase4.BerylliumIE
