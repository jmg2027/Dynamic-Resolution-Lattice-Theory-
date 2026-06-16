import E213.Meta.Int213.OrderMul

/-!
# Pythagorean-triple parametrization (∅-axiom)

Euclid's generator: for integers `m, n`, `(m²−n²)² + (2mn)² = (m²+n²)²`
(`pyth_param`) — a pure `ring_intZ` identity, the classical source of
Pythagorean triples.  With nondegeneracy from the Int213 order layer:

  * `leg1_pos` : the `m²−n²` leg is positive for `0 < n < m`;
  * `hyp_gt_leg1` : the hypotenuse `m²+n²` strictly dominates that leg;
  * `pyth_param_scaled` : every multiple `k·(triple)` is again a triple.

Genuinely absent (the corpus "Pythagorean" hits are physics mixing-angle docstrings).
All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PythagoreanTriples

open E213.Meta.Int213
open E213.Meta.Int213.Order
open E213.Meta.Int213.OrderMul

/-- ★ **Euclid's generator**: `(m²−n²)² + (2mn)² = (m²+n²)²`. -/
theorem pyth_param (m n : Int) :
    (m*m - n*n)*(m*m - n*n) + (2*m*n)*(2*m*n)
      = (m*m + n*n)*(m*m + n*n) := by ring_intZ

/-- The `m²−n²` leg factors as `(m−n)(m+n)`. -/
theorem leg_factor (m n : Int) : m*m - n*n = (m - n) * (m + n) := by ring_intZ

/-- **First leg positive** when `0 < n < m`. -/
theorem leg1_pos {m n : Int} (hn : 0 < n) (hnm : n < m) : 0 < m*m - n*n := by
  have hmn : 0 < m - n := sub_pos_of_lt hnm
  have hm : 0 < m := lt_trans hn hnm
  have hsum : 0 < m + n := by
    have hle : n ≤ m + n := by
      have h0 : (0 : Int) + n ≤ m + n := add_le_add_right (le_of_lt hm) n
      rwa [zero_add] at h0
    exact lt_of_lt_of_le hn hle
  have hpos : 0 < (m - n) * (m + n) := mul_pos hmn hsum
  rw [leg_factor m n]; exact hpos

/-- **Hypotenuse strictly dominates the `m²−n²` leg** when `0 < n`. -/
theorem hyp_gt_leg1 {m n : Int} (hn : 0 < n) : m*m - n*n < m*m + n*n := by
  apply lt_of_sub_pos
  rw [show (m*m + n*n) - (m*m - n*n) = 2*(n*n) by ring_intZ]
  exact mul_pos (by decide) (mul_pos hn hn)

/-- ★ **Scaled Euclid generator**: `(k(m²−n²))² + (k·2mn)² = (k(m²+n²))²`. -/
theorem pyth_param_scaled (k m n : Int) :
    (k*(m*m - n*n))*(k*(m*m - n*n)) + (k*(2*m*n))*(k*(2*m*n))
      = (k*(m*m + n*n))*(k*(m*m + n*n)) := by ring_intZ

/-! ## Concrete primitive-triple smokes -/

theorem triple_345 : (3:Int)*3 + 4*4 = 5*5 := by decide
theorem triple_51213 : (5:Int)*5 + 12*12 = 13*13 := by decide

/-- The `m=2,n=1` instance lands on legs `3,4` and hypotenuse `5`. -/
theorem inst_2_1_values :
    (2:Int)*2 - 1*1 = 3 ∧ 2*2*1 = 4 ∧ (2:Int)*2 + 1*1 = 5 := by decide

end E213.Lib.Math.NumberTheory.PythagoreanTriples
