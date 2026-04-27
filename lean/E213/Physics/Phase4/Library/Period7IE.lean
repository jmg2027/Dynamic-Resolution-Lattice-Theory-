import E213.Physics.SimplexCounts

/-!
# Period 7 (Z=87~118) — Fr ~ Og atomic catalog

32 원소 (actinides 90-103, super-heavy 104+).

## Z atomic clean cases

  Th  (90) = NS²·NT·d
  Am  (95) = d·(NS³-NT³)
  Cm  (96) = NT⁵·NS
  Cf  (98) = NT·(NS²-NT)²
  Fm (100) = NT²·d²
  Rf (104) = NT³·(NS²+NT²)
  Db (105) = NS·d·(NS²-NT)
  Hs (108) = NT²·NS³
  Cn (112) = NT⁴·(NS²-NT)
  Ts (117) = NS²·(NS²+NT²)
  Og (118) = 2·NS³ + 2·NT^d ★ Period 7 closure

## Observed IE (synthetic, theoretical for Z>104)

  Fr 4.073   Ra 5.279    Ac 5.380   Th 6.307
  U 6.194    Np 6.266    Pu 6.026   Am 5.974
  Og ~8.9 (predicted)

대부분 lanthanide/actinide 는 동일 valence (s² or s²f^k)
→ IE 가 Z 따라 천천히 증가.
-/

namespace E213.Physics.Phase4.Library.Period7IE

open E213.Physics.Simplex

theorem Z_Th : NS * NS * NT * d = 90 := by decide
theorem Z_Cm : NT * NT * NT * NT * NT * NS = 96 := by decide
theorem Z_Cf : NT * (NS * NS - NT) * (NS * NS - NT) = 98 := by decide
theorem Z_Fm : NT * NT * d * d = 100 := by decide
theorem Z_Hs : NT * NT * NS * NS * NS = 108 := by decide

/-- ★ Og Period 7 closure = 2·NS³ + 2·NT^d atomic. -/
theorem Z_Og : 2 * NS * NS * NS + 2 * (NT * NT * NT * NT * NT) = 118 := by decide

end E213.Physics.Phase4.Library.Period7IE
