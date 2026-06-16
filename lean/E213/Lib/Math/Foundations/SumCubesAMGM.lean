import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic

/-!
# Sum-of-cubes factorization + three-variable AM–GM over `Int` (∅-axiom)

  * ★★ `sum_cubes_factor` — `a³+b³+c³ − 3abc = (a+b+c)(a²+b²+c²−ab−bc−ca)`.
  * ★★ `sum_cubes_sos` — `2(a²+b²+c²−ab−bc−ca) = (a−b)²+(b−c)²+(c−a)²`.
  * ★★★ `amgm3` — for `0 ≤ a,b,c`, `3abc ≤ a³+b³+c³` (the cube-form AM–GM).
  * bonus `amgm2` (`2ab ≤ a²+b²`), `amgm2'` (`4ab ≤ (a+b)²`).

Complements the fixed-dim `Lib/Math/Foundations/Positivity.lean` (`amgm_2`,
`qm_am_3`, `prod_sum_le_sq_sum`).  Note (`^` vs `ring_intZ`): `ring_intZ` treats
`a^k` as an opaque atom; the `pow2`/`pow3` helpers bridge `a^k` to `*`-form
(`a^2 = 1·a·a` definitionally) before each `ring_intZ`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Foundations.SumCubesAMGM

open E213.Meta.Int213

/-- `a² = a·a` (npow reduces definitionally to `1·a·a`). -/
theorem pow2 (a : Int) : a^2 = a*a := by
  have h : a^2 = 1*a*a := rfl
  rw [h]; ring_intZ

/-- `a³ = a·a·a`. -/
theorem pow3 (a : Int) : a^3 = a*a*a := by
  have h : a^3 = 1*a*a*a := rfl
  rw [h]; ring_intZ

/-- ★★ **Sum-of-cubes factorization** (ℤ):
    `a³+b³+c³ − 3abc = (a+b+c)(a²+b²+c²−ab−bc−ca)`. -/
theorem sum_cubes_factor (a b c : Int) :
    a^3 + b^3 + c^3 - 3*a*b*c
      = (a + b + c) * (a^2 + b^2 + c^2 - a*b - b*c - c*a) := by
  rw [pow3 a, pow3 b, pow3 c, pow2 a, pow2 b, pow2 c]
  ring_intZ

/-- ★★ **SOS form of the quadratic factor** (ℤ):
    `2(a²+b²+c²−ab−bc−ca) = (a−b)²+(b−c)²+(c−a)²`. -/
theorem sum_cubes_sos (a b c : Int) :
    2*(a^2 + b^2 + c^2 - a*b - b*c - c*a)
      = (a-b)^2 + (b-c)^2 + (c-a)^2 := by
  rw [pow2 a, pow2 b, pow2 c, pow2 (a-b), pow2 (b-c), pow2 (c-a)]
  ring_intZ

/-- The quadratic factor is nonnegative (`twice` it is the SOS above). -/
theorem sos_factor_nonneg (a b c : Int) :
    0 ≤ a^2 + b^2 + c^2 - a*b - b*c - c*a := by
  apply nonneg_of_add_self
  have hdouble : (a^2 + b^2 + c^2 - a*b - b*c - c*a)
                 + (a^2 + b^2 + c^2 - a*b - b*c - c*a)
               = (a-b)*(a-b) + ((b-c)*(b-c) + (c-a)*(c-a)) := by
    rw [pow2 a, pow2 b, pow2 c]; ring_intZ
  rw [hdouble]
  exact add_nonneg (int_sq_nonneg (a-b))
    (add_nonneg (int_sq_nonneg (b-c)) (int_sq_nonneg (c-a)))

/-- ★★★ **Three-variable AM–GM** (cube form, ℤ): for `0 ≤ a,b,c`,
    `3abc ≤ a³+b³+c³` (arithmetic mean of `a³,b³,c³` ≥ geometric `abc`). -/
theorem amgm3 (a b c : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3*a*b*c ≤ a^3 + b^3 + c^3 := by
  have hsum : 0 ≤ a + b + c := add_nonneg (add_nonneg ha hb) hc
  have hfac : 0 ≤ a^2 + b^2 + c^2 - a*b - b*c - c*a := sos_factor_nonneg a b c
  have hprod : 0 ≤ (a + b + c) * (a^2 + b^2 + c^2 - a*b - b*c - c*a) :=
    mul_nonneg hsum hfac
  rw [← sum_cubes_factor a b c] at hprod
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hprod)

/-- bonus ★★ **2-variable AM–GM** `2ab ≤ a²+b²`, gap `(a−b)²`. -/
theorem amgm2 (a b : Int) : 2*a*b ≤ a^2 + b^2 := by
  have hgap : a^2 + b^2 - 2*a*b = (a-b)^2 := by
    rw [pow2 a, pow2 b, pow2 (a-b)]; ring_intZ
  have hpos : 0 ≤ a^2 + b^2 - 2*a*b := by
    rw [hgap, pow2 (a-b)]; exact int_sq_nonneg (a-b)
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hpos)

/-- bonus ★★ `4ab ≤ (a+b)²`, gap `(a−b)²`. -/
theorem amgm2' (a b : Int) : 4*a*b ≤ (a+b)^2 := by
  have hgap : (a+b)^2 - 4*a*b = (a-b)^2 := by
    rw [pow2 (a+b), pow2 (a-b)]; ring_intZ
  have hpos : 0 ≤ (a+b)^2 - 4*a*b := by
    rw [hgap, pow2 (a-b)]; exact int_sq_nonneg (a-b)
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hpos)

end E213.Lib.Math.Foundations.SumCubesAMGM
