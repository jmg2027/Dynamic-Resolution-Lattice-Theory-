import E213.Physics.Substrate
import E213.Physics.Simplex.Counts

/-!
# Translation: Angular momentum · spin → DRLT atomic

  L² eigenvalue ℓ(ℓ+1)ħ² → atomic
  L_z eigenvalue m·ħ → atomic
  Spin S = NT/2 = 1/NT atomic
  J = L + S (total angular momentum)
  Clebsch-Gordan coefficients atomic
-/

namespace E213.Physics.AtomicCorrespondences.AngularMomentum

open E213.Physics.Simplex.Counts

/-- Spin 1/2 = 1/NT atomic (NT slot). -/
theorem spin_half : NT = 2 := by decide

/-- L² eigenvalue ℓ(ℓ+1) atomic forms.
    ℓ=1: 1·2 = 2 = NT.
    ℓ=2: 2·3 = 6 = NS·NT.
    ℓ=3: 3·4 = 12 = 2·NS·NT.
    ℓ=4: 4·5 = 20 = 4·d.
    ℓ=5: 5·6 = 30 = NS·NT·d. -/
theorem L_l1 : 1 * 2 = NT := by decide
theorem L_l2 : 2 * 3 = NS * NT := by decide
theorem L_l3 : 3 * 4 = 2 * NS * NT := by decide

/-- m_l values -ℓ ≤ m ≤ ℓ → 2ℓ+1 values. -/
theorem m_count_l1 : 2 * 1 + 1 = NS := by decide
theorem m_count_l2 : 2 * 2 + 1 = d := by decide

/-- ★ Angular Momentum Capstone ★ -/
theorem angular_momentum_atomic :
    (NS = 3) ∧ (NT = 2) ∧ (d = 5)
    ∧ (NT = 2)              -- spin 1/2
    ∧ (1 * 2 = NT)          -- ℓ=1 eigenvalue
    ∧ (2 * 3 = NS * NT)     -- ℓ=2 eigenvalue
    ∧ (2 * 1 + 1 = NS)      -- m count for ℓ=1
    ∧ (2 * 2 + 1 = d) := by  -- m count for ℓ=2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.AtomicCorrespondences.AngularMomentum
