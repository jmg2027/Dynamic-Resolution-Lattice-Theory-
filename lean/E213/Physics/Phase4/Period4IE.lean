import E213.Physics.SimplexCounts

/-!
# Phase 4 Period4IE — Period 4 (K ~ Kr) atomic catalog

Period 4 = 18 elements (K to Kr, Z = 19-36).
Period 4 closure: Kr at Z = 36 = 6² = (NS·NT)² atomic.

## Z atomic forms

  K  (19) = NS³ - NT³ atomic (discovered in Phase 3)
  Ca (20) = 4·d atomic
  Sc (21) = NS·d + NS·NT atomic (= 15+6=21)
  Ti (22) = 2·d² - NT² + NT² ... or 22 = d²-NS atomic (= Cabibbo λ denom!)
  V  (23) = ? (no clean form)
  Cr (24) = d²-1 atomic (Phase 3)
  Mn (25) = d² atomic (Phase 3)
  Fe (26) = d²+1
  Co (27) = NS³ atomic
  Ni (28) = NS·d + NS·NT·NT - NT
  Cu (29) = ?
  Zn (30) = NS·NT·d atomic = 1/α_2 (Phase 3)
  Ga (31) = ?
  Ge (32) = NT^d = 2^5 atomic (Phase 3)
  As (33) = ?
  Se (34) = ?
  Br (35) = ?
  Kr (36) = (NS·NT)² atomic = 6² ★ Period 4 closure
-/

namespace E213.Physics.Phase4.Period4IE

open E213.Physics.Simplex

/-- Z atomic forms (clean cases). -/
theorem Z_K_atomic : NS * NS * NS - NT * NT * NT = 19 := by decide
theorem Z_Ca_atomic : 4 * d = 20 := by decide
theorem Z_Ti_atomic : d * d - NS = 22 := by decide
theorem Z_Cr_atomic : d * d - 1 = 24 := by decide
theorem Z_Mn_atomic : d * d = 25 := by decide
theorem Z_Co_atomic : NS * NS * NS = 27 := by decide
theorem Z_Zn_atomic : NS * NT * d = 30 := by decide
theorem Z_Ge_atomic : NT * NT * NT * NT * NT = 32 := by decide

/-- ★ Kr Period 4 closure = (NS·NT)² atomic. -/
theorem Z_Kr_atomic : (NS * NT) * (NS * NT) = 36 := by decide

/-- Period 4 size = 18 = 2·NS². -/
theorem period_4_size : 2 * NS * NS = 18 := by decide

/-- Period 4 closure = Period 3 close + Period 4 size. -/
theorem period_4_closure : 18 + 18 = 36 := by decide

end E213.Physics.Phase4.Period4IE
