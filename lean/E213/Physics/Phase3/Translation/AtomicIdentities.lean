import E213.Physics.Phase2
import E213.Physics.SimplexCounts

/-!
# Translation: Atomic 격자 의 *수치 항등식* catalog

★ DRLT atomic primitives 가 만족하는 *놀라운* 수치 항등식 ★

## 항등식 catalog

  (1) NS - NT = 1
  (2) NS·NT - 1 = NS² - NT²
  (3) NS² - NT² = NS + NT = d
  (4) NS² + NS = NT·d + ε  (ε small)
  (5) d·NT - NS² = 1 (Cassini at d=5)
  (6) d² = (NS+NT)² = NS² + 2NS·NT + NT²
  (7) NS² - 1 = NS·NT + (NT² - 2)
  (8) F_n F_{n+2} - F_{n+1}² = (-1)^n  (Cassini)

(3) 가 특별: NS² - NT² = NS + NT 는 *모든* (NS, NT) 에 성립
하는 게 아니다.  *NS - NT = 1 일 때* 만 성립.
   → atomic asymmetry NS-NT = 1 의 직접 결과.
-/

namespace E213.Physics.Phase3.Translation.AtomicIdentities

open E213.Physics.Simplex

/-- (1) NS - NT = 1 atomic asymmetry. -/
theorem id_1 : NS - NT = 1 := by decide

/-- (2) NS·NT - 1 = NS² - NT². -/
theorem id_2 : NS * NT - 1 = NS * NS - NT * NT := by decide

/-- (3) NS² - NT² = d.  Striking: NS² - NT² = NS + NT atomic. -/
theorem id_3 : NS * NS - NT * NT = NS + NT := by decide

/-- (4) NS² - NT² = d (다른 표현). -/
theorem id_4 : NS * NS - NT * NT = d := by decide

/-- (5) Cassini: d·NT - NS² = 1. -/
theorem id_5 : d * NT - NS * NS = 1 := by decide

/-- (6) d² = NS² + 2NS·NT + NT² = 25. -/
theorem id_6 : d * d = NS * NS + 2 * NS * NT + NT * NT := by decide

/-- (7) NS² - 1 = NS·NT + (NT² - 2): 8 = 6 + 2 ★. -/
theorem id_7 : NS * NS - 1 = NS * NT + NT * NT - NT := by decide

/-- ★ Atomic Identities Capstone ★ -/
theorem atomic_identities :
    -- (1) atomic asymmetry
    (NS - NT = 1)
    -- (2) cross identity
    ∧ (NS * NT - 1 = NS * NS - NT * NT)
    -- (3) NS² - NT² = NS + NT (because NS - NT = 1)
    ∧ (NS * NS - NT * NT = NS + NT)
    -- (4) = d
    ∧ (NS * NS - NT * NT = d)
    -- (5) Cassini
    ∧ (d * NT - NS * NS = 1)
    -- (6) (NS+NT)² = d²
    ∧ (d * d = NS * NS + 2 * NS * NT + NT * NT) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase3.Translation.AtomicIdentities
