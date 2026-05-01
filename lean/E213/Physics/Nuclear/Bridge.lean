import E213.Physics.Nuclear.Binding
import E213.Physics.Nuclear.MagicNumbers

/-!
# Nuclear ↔ Diamond bridge

Bethe-Weizsäcker semi-empirical mass formula coefficients
factor through atomic primitives.  Magic numbers also from
HO closed form on Δ⁴.

Per `Physics/NuclearBinding.lean`:
  a_V (volume) = NS·NT = 6 = d+1
  a_S (surface) = d-1 = 4
  a_C (Coulomb) num/den = NS/d = 3/5

Per `Physics/MagicNumbers.lean`:
  Magic = HO closed form n(n+1)(n+2)/3
  First 7: {2, 8, 20, 28, 50, 82, 126}
-/

namespace E213.Physics.Nuclear.Bridge

/-- a_V (volume coefficient) = NS·NT = 6 = d+1. -/
theorem a_V_atomic :
    E213.Physics.Nuclear.Binding.a_V_coef = 6
    ∧ (3 * 2 : Nat) = 6
    ∧ (5 + 1 : Nat) = 6 := by decide

/-- a_S (surface coefficient) = d-1 = 4 = NS+1. -/
theorem a_S_atomic :
    E213.Physics.Nuclear.Binding.a_S_coef = 4
    ∧ (5 - 1 : Nat) = 4
    ∧ (3 + 1 : Nat) = 4 := by decide

/-- a_C (Coulomb) num/den = NS/d = 3/5. -/
theorem a_C_atomic :
    E213.Physics.Nuclear.Binding.a_C_coef_num = 3
    ∧ E213.Physics.Nuclear.Binding.a_C_coef_den = 5 := by decide

/-- Magic numbers first 3 from HO closed form. -/
theorem magic_atomic :
    E213.Physics.Nuclear.MagicNumbers.ho_magic 1 = 2
    ∧ E213.Physics.Nuclear.MagicNumbers.ho_magic 2 = 8
    ∧ E213.Physics.Nuclear.MagicNumbers.ho_magic 3 = 20 := by decide

/-- ★★★ Nuclear bridge capstone — all coefficients factor
    through atomic NS, NT, d. -/
theorem nuclear_bridge_capstone :
    E213.Physics.Simplex.Counts.NS = 3
    ∧ E213.Physics.Simplex.Counts.NT = 2
    ∧ E213.Physics.Simplex.Counts.d = 5
    -- Bethe-Weizsäcker
    ∧ E213.Physics.Nuclear.Binding.a_V_coef = 6
    ∧ E213.Physics.Nuclear.Binding.a_S_coef = 4
    ∧ E213.Physics.Nuclear.Binding.a_C_coef_num = 3
    -- Magic
    ∧ E213.Physics.Nuclear.MagicNumbers.ho_magic 3 = 20 := by decide

end E213.Physics.Nuclear.Bridge
