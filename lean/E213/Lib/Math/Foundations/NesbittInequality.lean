import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic

/-!
# AM–HM core + Nesbitt's inequality over `Int` (∅-axiom)

  * ★★★ `am_hm_core` — for `0 ≤ x,y,z`,
      `9*x*y*z ≤ (x+y+z)*(x*y+y*z+z*x)`.
    SOS identity: `(x+y+z)*(xy+yz+zx) − 9xyz
                    = x*(y−z)*(y−z) + y*(z−x)*(z−x) + z*(x−y)*(x−y)`.
  * ★★ `nesbitt_cleared` — Nesbitt's inequality in denominator-cleared form
    (`a/(b+c)+b/(c+a)+c/(a+b) ≥ 3/2` after clearing), for `0 ≤ a,b,c`:
      `3*(a+b)*(b+c)*(c+a)
        ≤ 2*(a*(a+c)*(a+b) + b*(b+a)*(b+c) + c*(c+b)*(c+a))`.
    Proved by its own `ring_intZ` SOS split into `var·(diff)²` terms.

All ∅-axiom (reuses `E213.Meta.Int213` PURE order primitives).
-/

namespace E213.Lib.Math.Foundations.NesbittInequality

open E213.Meta.Int213

/-- ★★★ **AM–HM core** (ℤ): for `0 ≤ x,y,z`,
    `9xyz ≤ (x+y+z)(xy+yz+zx)`. -/
theorem am_hm_core {x y z : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    9*x*y*z ≤ (x+y+z)*(x*y+y*z+z*x) := by
  -- SOS identity for the difference
  have hid : (x+y+z)*(x*y+y*z+z*x) - 9*x*y*z
      = x*((y-z)*(y-z)) + (y*((z-x)*(z-x)) + z*((x-y)*(x-y))) := by
    ring_intZ
  -- each summand nonneg: nonneg var times a square
  have h1 : 0 ≤ x*((y-z)*(y-z)) := mul_nonneg hx (int_sq_nonneg (y-z))
  have h2 : 0 ≤ y*((z-x)*(z-x)) := mul_nonneg hy (int_sq_nonneg (z-x))
  have h3 : 0 ≤ z*((x-y)*(x-y)) := mul_nonneg hz (int_sq_nonneg (x-y))
  have hpos : 0 ≤ (x+y+z)*(x*y+y*z+z*x) - 9*x*y*z := by
    rw [hid]; exact add_nonneg h1 (add_nonneg h2 h3)
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hpos)

/-- ★★ **Nesbitt's inequality** (denominator-cleared form, ℤ): for `0 ≤ a,b,c`,
    `3(a+b)(b+c)(c+a) ≤ 2(a(a+c)(a+b) + b(b+a)(b+c) + c(c+b)(c+a))`.
    Equivalent (over the positives) to `a/(b+c)+b/(c+a)+c/(a+b) ≥ 3/2`.
    This is exactly the AM–HM core at `x=b+c, y=c+a, z=a+b`; here proved by
    its own `ring_intZ` SOS split into `var·(diff)²` terms. -/
theorem nesbitt_cleared {a b c : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3*(a+b)*(b+c)*(c+a)
      ≤ 2*(a*(a+c)*(a+b) + b*(b+a)*(b+c) + c*(c+b)*(c+a)) := by
  -- own SOS split: difference = (b+c)(c−b)² + (c+a)(a−c)² + (a+b)(b−a)²
  -- (the AM–HM core SOS at x=b+c, y=c+a, z=a+b).
  have hid : 2*(a*(a+c)*(a+b) + b*(b+a)*(b+c) + c*(c+b)*(c+a))
                - 3*(a+b)*(b+c)*(c+a)
      = (b+c)*((c-b)*(c-b)) + ((c+a)*((a-c)*(a-c)) + (a+b)*((b-a)*(b-a))) := by
    ring_intZ
  have hbc : 0 ≤ b + c := add_nonneg hb hc
  have hca : 0 ≤ c + a := add_nonneg hc ha
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have h1 : 0 ≤ (b+c)*((c-b)*(c-b)) := mul_nonneg hbc (int_sq_nonneg (c-b))
  have h2 : 0 ≤ (c+a)*((a-c)*(a-c)) := mul_nonneg hca (int_sq_nonneg (a-c))
  have h3 : 0 ≤ (a+b)*((b-a)*(b-a)) := mul_nonneg hab (int_sq_nonneg (b-a))
  have hpos : 0 ≤ 2*(a*(a+c)*(a+b) + b*(b+a)*(b+c) + c*(c+b)*(c+a))
                  - 3*(a+b)*(b+c)*(c+a) := by
    rw [hid]; exact add_nonneg h1 (add_nonneg h2 h3)
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hpos)

/-! ### Concrete smokes (closed terms, `decide`). Equality at `x=y=z`. -/

example : 9*(1:Int)*1*1 ≤ (1+1+1)*(1*1+1*1+1*1) := by decide
example : 9*(2:Int)*2*2 ≤ (2+2+2)*(2*2+2*2+2*2) := by decide
example : 9*(1:Int)*2*3 ≤ (1+2+3)*(1*2+2*3+3*1) := by decide
example : 9*(0:Int)*5*7 ≤ (0+5+7)*(0*5+5*7+7*0) := by decide
-- Nesbitt smoke
example : 3*((1:Int)+1)*(1+1)*(1+1)
    ≤ 2*(1*(1+1)*(1+1) + 1*(1+1)*(1+1) + 1*(1+1)*(1+1)) := by decide
example : 3*((1:Int)+2)*(2+3)*(3+1)
    ≤ 2*(1*(1+3)*(1+2) + 2*(2+1)*(2+3) + 3*(3+2)*(3+1)) := by decide

end E213.Lib.Math.Foundations.NesbittInequality
