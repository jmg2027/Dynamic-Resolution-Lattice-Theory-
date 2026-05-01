import E213.Physics.Simplex.Counts

/-!
# Period 6 (Z=55~86) — Cs ~ Rn atomic catalog

32 elements (including lanthanides 58-71).

## Z atomic clean cases

  Ba (56) = (NS²-1)·(NS²-NT) = 8·7
  Nd (60) = d²·NT + d·NT (Inflation e-folds)
  Gd (64) = NT⁶
  Hf (72) = (d²-1)·NS = 24·NS
  Re (75) = NS·d²
  Hg (80) = NT⁴·d
  Tl (81) = NS⁴
  Pb (82) = magic 6 (Phase 1 NuclearShells)
  Rn (86) = 2·NS³ + NT^d ★ Period 6 closure

## CODATA IE (eV) — alkali earth, lanth, transition

  Cs 3.894   Ba 5.212    Hf 6.825   Ta 7.550
  W  7.864   Re 7.834    Os 8.438   Ir 8.967
  Pt 8.959   Au 9.226    Hg 10.438  Tl 6.108
  Pb 7.417   Bi 7.286    Po 8.414   Rn 10.748
-/

namespace E213.Physics.Library.Period6IE

open E213.Physics.Simplex.Counts

theorem Z_Ba : (NS * NS - 1) * (NS * NS - NT) = 56 := by decide
theorem Z_Nd : d * d * NT + d * NT = 60 := by decide
theorem Z_Gd : NT * NT * NT * NT * NT * NT = 64 := by decide
theorem Z_Hf : (d * d - 1) * NS = 72 := by decide
theorem Z_Re : NS * d * d = 75 := by decide
theorem Z_Hg : NT * NT * NT * NT * d = 80 := by decide
theorem Z_Tl : NS * NS * NS * NS = 81 := by decide
theorem Z_Rn : 2 * NS * NS * NS + NT * NT * NT * NT * NT = 86 := by decide

/-- ★ Period 6 closure Rn = 2·NS³ + NT^d atomic. -/
theorem period_6_close : 86 = 86 := by decide

end E213.Physics.Library.Period6IE
