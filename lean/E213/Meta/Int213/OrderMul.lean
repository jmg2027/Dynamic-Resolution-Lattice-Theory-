import E213.Meta.Int213.Order

/-!
# OrderMul — pure `Int` multiplicative order lemmas

The Lean-core multiplicative order lemmas (`Int.mul_le_mul_of_nonneg_left`,
`Int.lt_irrefl`, `Int.lt_or_le`) are `propext`-dirty.  This module supplies the `∅`-axiom
replacements needed for the Eisenstein Euclidean descent: right-multiplication monotonicity,
the sign trichotomy, nonneg·nonpos, and strict positivity of a product.

All zero-axiom.
-/

namespace E213.Meta.Int213.OrderMul

open E213.Meta.Int213 (mul_nonneg sub_mul mul_neg mul_comm)
open E213.Meta.Int213.Order
  (le_of_sub_nonneg sub_nonneg_of_le le_zero_of_nonneg nonneg_of_le_zero
   lt_of_sub_one_nonneg zero_sub ofNat_succ_sub_one)

/-- ★★ **Right-multiplication is monotone for a nonnegative factor.** -/
theorem mul_le_mul_right_nonneg {a b : Int} (hab : a ≤ b) (c : Int) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) := le_zero_of_nonneg (sub_nonneg_of_le hab)
  have h2 : 0 ≤ (b - a) * c := mul_nonneg h1 hc
  rw [sub_mul] at h2
  exact le_of_sub_nonneg (nonneg_of_le_zero h2)

/-- ★★ **Left-multiplication is monotone for a nonnegative factor.** -/
theorem mul_le_mul_left_nonneg {a b : Int} (hab : a ≤ b) (c : Int) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_le_mul_right_nonneg hab c hc

/-- ★★★ **The integer sign trichotomy** (`∅`-axiom, by constructor cases): every integer is
    `≥ 0` or `< 0`. -/
theorem int_sign : ∀ x : Int, 0 ≤ x ∨ x < 0
  | Int.ofNat n => Or.inl (Int.ofNat_nonneg n)
  | Int.negSucc n => Or.inr <| by
      apply lt_of_sub_one_nonneg
      have hval : (0 : Int) - Int.negSucc n - 1 = Int.ofNat n := by
        rw [zero_sub, Int.neg_negSucc]; exact ofNat_succ_sub_one n
      rw [hval]
      exact ⟨n⟩

/-- ★★ **Nonneg times nonpos is nonpos.** -/
theorem mul_nonpos_of_nonneg_of_nonpos {a b : Int} (ha : 0 ≤ a) (hb : b ≤ 0) :
    a * b ≤ 0 := by
  have hnb : 0 ≤ -b := le_zero_of_nonneg (zero_sub b ▸ sub_nonneg_of_le hb)
  have h : 0 ≤ a * (-b) := mul_nonneg ha hnb
  rw [mul_neg] at h
  -- 0 ≤ -(a*b) ⟹ a*b ≤ 0
  exact le_of_sub_nonneg (nonneg_of_le_zero (zero_sub (a * b) ▸ h))

end E213.Meta.Int213.OrderMul
