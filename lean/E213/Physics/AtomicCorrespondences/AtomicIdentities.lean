import E213.Physics.Substrate
import E213.Physics.Simplex.Counts

/-!
# Translation: *Numerical identity* catalog of the atomic lattice

★ Remarkable numerical identities satisfied by DRLT atomic primitives ★

## Identity catalog

  (1) NS - NT = 1
  (2) NS·NT - 1 = NS² - NT²
  (3) NS² - NT² = NS + NT = d
  (4) NS² + NS = NT·d + ε  (ε small)
  (5) d·NT - NS² = 1 (Cassini at d=5)
  (6) d² = (NS+NT)² = NS² + 2NS·NT + NT²
  (7) NS² - 1 = NS·NT + (NT² - 2)
  (8) F_n F_{n+2} - F_{n+1}² = (-1)^n  (Cassini)

(3) is special: NS² - NT² = NS + NT does NOT hold for *all* (NS, NT).
It holds *only when* NS - NT = 1.
   → Direct consequence of atomic asymmetry NS-NT = 1.
-/

namespace E213.Physics.AtomicCorrespondences.AtomicIdentities

open E213.Physics.Simplex.Counts

/-- (1) NS - NT = 1 atomic asymmetry. -/
theorem id_1 : NS - NT = 1 := by decide

/-- (2) NS·NT - 1 = NS² - NT². -/
theorem id_2 : NS * NT - 1 = NS * NS - NT * NT := by decide

/-- (3) NS² - NT² = d.  Striking: NS² - NT² = NS + NT atomic. -/
theorem id_3 : NS * NS - NT * NT = NS + NT := by decide

/-- (4) NS² - NT² = d (alternative form). -/
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

end E213.Physics.AtomicCorrespondences.AtomicIdentities
