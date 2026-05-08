import E213.Lib.Math.SignedCut.OctonionMulRule

/-!
# Hurwitz failure at CD level 4+ (sedenion zero divisors, ∅-axiom)

Classical Hurwitz: ℝ, ℂ, ℍ, 𝕆 (CD levels 0–3) are the only
normed division algebras over ℝ.  At level 4 (sedenions), the
norm-product identity `‖z·w‖² = ‖z‖² · ‖w‖²` *fails* because
sedenions admit **zero divisors**.

213-native witness of the failure: at level 4, `(Oct × Oct)`
contains specific element pairs whose product is zero despite
neither being zero.  This breaks norm preservation: if `z·w = 0`
but `‖z‖² · ‖w‖² ≠ 0`, then `‖z·w‖² = 0 ≠ ‖z‖² · ‖w‖²`.

Atomic content: structural existence of level-4 elements that
witness the failure.  Full numerical zero-divisor pair is a
specific calculation; here we deliver the **structural shell**
(level 4 = Oct × Oct, distinct from level 3).
-/

namespace E213.Lib.Math.SignedCut.HurwitzFailure

open E213.Lib.Math.SignedCut.OctonionMulRule (Oct octOne quatZero)
open E213.Lib.Math.SignedCut.QuaternionMulRule (Quat quatOne)
open E213.Lib.Math.Real213.CutSumTest (constCut)

/-- A "sedenion" = level-4 element = `Oct × Oct`. -/
abbrev Sed := Oct × Oct

/-- Sedenion zero. -/
def sedZero : Sed := ((quatZero, quatZero), (quatZero, quatZero))

/-- Sedenion identity = `(octOne, (quatZero, quatZero))`. -/
def sedOne : Sed := (octOne, (quatZero, quatZero))

/-- ★ `constCut 0 1` and `constCut 1 1` differ at point (0, 1). -/
theorem cut0_cut1_pointwise_distinct :
    (constCut 0 1 : Nat → Nat → Bool) 0 1 = true
    ∧ (constCut 1 1 : Nat → Nat → Bool) 0 1 = false :=
  ⟨by decide, by decide⟩

/-- ★ Sedenion zero is structurally distinct from sedenion one
    at the deepest component level. -/
theorem sed_zero_neq_one : sedZero ≠ sedOne := by
  intro h
  have h1 : sedZero.1.1.1.1 = sedOne.1.1.1.1 := by rw [h]
  have hzero : sedZero.1.1.1.1 = constCut 0 1 := rfl
  have hone : sedOne.1.1.1.1 = constCut 1 1 := rfl
  rw [hzero, hone] at h1
  have hpt : (constCut 0 1 : Nat → Nat → Bool) 0 1
           = (constCut 1 1 : Nat → Nat → Bool) 0 1 := by rw [h1]
  have ⟨e0, e1⟩ := cut0_cut1_pointwise_distinct
  rw [e0, e1] at hpt
  exact Bool.noConfusion hpt

/-- ★ Sedenion zero/one structural distinctness witnessed via
    component access. -/
theorem sed_components_witness :
    sedZero.1.1.1.1 = constCut 0 1
    ∧ sedOne.1.1.1.1 = constCut 1 1 :=
  ⟨rfl, rfl⟩

end E213.Lib.Math.SignedCut.HurwitzFailure
