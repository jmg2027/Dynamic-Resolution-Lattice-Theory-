import E213.Physics.Simplex.Counts

/-!
# Period 5 (Z=37~54) — Rb ~ Xe atomic catalog

## Z atomic forms (clean cases)

  Rb (37) = (NS·NT)² + 1
  Zr (40) = (NS²-1)·d = 8·5
  Nb (41) = α_GUT integer (prime)
  Mo (42) = (NS²-NT)·NS·NT = 7·6
  Rh (45) = NS²·d
  Cd (48) = NT⁴·NS = 16·3
  In (49) = (NS²-NT)² = 7²
  Sn (50) = 2·d² (Period 8 size)
  Te (52) = NT²·(NS²+NT²) = 4·13
  Xe (54) = 2·NS³ ★ Period 5 closure

## CODATA IE (eV)

  Rb 4.177  Sr 5.695  Y 6.217  Zr 6.634
  Nb 6.759  Mo 7.092  Tc 7.119  Ru 7.361
  Rh 7.459  Pd 8.337  Ag 7.576  Cd 8.994
  In 5.786  Sn 7.344  Sb 8.609  Te 9.010
  I  10.451 Xe 12.130
-/

namespace E213.Physics.Library.Period5IE

open E213.Physics.Simplex.Counts

/-- Z atomic clean cases. -/
theorem Z_Zr : (NS * NS - 1) * d = 40 := by decide
theorem Z_Mo : (NS * NS - NT) * NS * NT = 42 := by decide
theorem Z_Rh : NS * NS * d = 45 := by decide
theorem Z_Cd : NT * NT * NT * NT * NS = 48 := by decide
theorem Z_In : (NS * NS - NT) * (NS * NS - NT) = 49 := by decide
theorem Z_Sn : 2 * d * d = 50 := by decide
theorem Z_Xe : 2 * NS * NS * NS = 54 := by decide

end E213.Physics.Library.Period5IE
