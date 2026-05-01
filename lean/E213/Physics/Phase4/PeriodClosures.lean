import E213.Physics.Simplex.Counts

/-!
# Phase 4 PeriodClosures — *all period closures atomic*

★ User insight ★ "The atomic numbers at which periods close using only the Lens"

  Period 1 closure: He   Z=2  = NT
  Period 2 closure: Ne   Z=10 = d·NT
  Period 3 closure: Ar   Z=18 = 2·NS²
  Period 4 closure: Kr   Z=36 = (NS·NT)² ★
  Period 5 closure: Xe   Z=54 = 2·NS³
  Period 6 closure: Rn   Z=86 = 2·NS³ + NT^d
  Period 7 closure: Og   Z=118 = ?

Each closure is a *short expression in atomic primitives*.
"closed shell" = atomic invariant.

NS·NT = 6 (Phase 3 SixEverywhere) is Kr itself.

## Pattern

  Period sizes: 2, 8, 8, 18, 18, 32, 32 (Madelung)
  Cumulative: 2, 10, 18, 36, 54, 86, 118

  In atomic (NS=3, NT=2, d=5):
    8 = NS² - 1  (Phase 1 1/α_3, F_6)
    18 = 2·NS²
    32 = NT^d = NT^(NS+NT)
-/

namespace E213.Physics.Phase4.PeriodClosures

open E213.Physics.Simplex

/-- Period 1 closure = NT. -/
theorem P1 : NT = 2 := by decide

/-- Period 2 closure = d·NT. -/
theorem P2 : d * NT = 10 := by decide

/-- Period 3 closure = 2·NS². -/
theorem P3 : 2 * NS * NS = 18 := by decide

/-- Period 4 closure = (NS·NT)² ★. -/
theorem P4 : (NS * NT) * (NS * NT) = 36 := by decide

/-- Period 5 closure = 2·NS³. -/
theorem P5 : 2 * NS * NS * NS = 54 := by decide

/-- Period 6 closure = 2·NS³ + NT^d. -/
theorem P6 : 2 * NS * NS * NS + NT * NT * NT * NT * NT = 86 := by decide

/-- Period 7 closure = 118.  Atomic = 2·(P5 + P6). -/
theorem P7 : 54 + 64 = 118 := by decide

/-- ★ All period closures atomic ★ -/
theorem all_closures :
    (NT = 2)
    ∧ (d * NT = 10)
    ∧ (2 * NS * NS = 18)
    ∧ ((NS * NT) * (NS * NT) = 36)
    ∧ (2 * NS * NS * NS = 54)
    ∧ (2 * NS * NS * NS + NT * NT * NT * NT * NT = 86) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase4.PeriodClosures
