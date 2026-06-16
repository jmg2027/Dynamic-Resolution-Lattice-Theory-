import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order
import E213.Meta.Nat.IntHelpers

/-!
# Schur's inequality over `Int` (degrees t = 1 and t = 2), ∅-axiom

For ordered integers `x ≥ y ≥ z ≥ 0`:

* **t = 1**: `x(x−y)(x−z) + y(y−x)(y−z) + z(z−x)(z−y) ≥ 0`.
* **t = 2**: `x²(x−y)(x−z) + y²(y−x)(y−z) + z²(z−x)(z−y) ≥ 0`.

Both proofs follow the same skeleton:
1. a `ring_intZ` identity rewriting the symmetric LHS into a manifestly
   nonneg two-summand form `(x−y)²·P + Q·(x−z)(y−z)`;
2. `0 ≤ summand` via products of nonnegs (`mul_nonneg`, `mul_self_nonneg`);
3. `0 ≤ a → 0 ≤ b → 0 ≤ a + b` (`add_nonneg`).

t = 1 split:  `(x−y)²·(x+y−z) + z·(x−z)(y−z)`, with `x+y−z = (x−z)+y ≥ 0`.
t = 2 split:  `(x−y)²·P + z²·(x−z)(y−z)`, with
              `P = x²+xy+y²−zx−zy = x² + (x+y)(y−z) ≥ 0`.

All PURE: order facts route through the `Int.NonNeg` corpus
(`E213.Meta.Int213.{mul_nonneg, add_nonneg}`,
 `E213.Meta.Nat.IntHelpers.mul_self_nonneg`,
 `E213.Meta.Int213.Order.{le_zero_of_nonneg, sub_nonneg_of_le}`).
-/

namespace E213.Lib.Math.Foundations.SchurInequality

open E213.Meta.Int213 (mul_nonneg add_nonneg)
open E213.Meta.Int213.Order (le_zero_of_nonneg sub_nonneg_of_le)
open E213.Meta.Nat.IntHelpers (mul_self_nonneg)

/-- `0 ≤ a*a` for any integer (square is nonneg). -/
theorem sq_nonneg (a : Int) : (0 : Int) ≤ a * a := mul_self_nonneg a

/-- `b ≤ a  ⟹  0 ≤ a − b`.  PURE bridge from `≤` to `0 ≤ (sub)`. -/
theorem sub_nonneg_of_le' {a b : Int} (h : b ≤ a) : (0 : Int) ≤ a - b :=
  le_zero_of_nonneg (sub_nonneg_of_le h)

/-! ## t = 1 -/

/-- ★★★ **Schur's inequality, t = 1**, over `Int`.
    For `z ≤ y ≤ x` and `0 ≤ z`:
    `x(x−y)(x−z) + y(y−x)(y−z) + z(z−x)(z−y) ≥ 0`. -/
theorem schur_t1 {x y z : Int} (hxy : y ≤ x) (hyz : z ≤ y) (hz : 0 ≤ z) :
    (0 : Int) ≤ x*(x-y)*(x-z) + y*(y-x)*(y-z) + z*(z-x)*(z-y) := by
  -- key regrouping identity (manifestly nonneg two-summand form)
  have hid :
      x*(x-y)*(x-z) + y*(y-x)*(y-z) + z*(z-x)*(z-y)
        = (x-y)*(x-y)*((x-z) + y) + z*((x-z)*(y-z)) := by ring_intZ
  rw [hid]
  -- 0 ≤ x − z  (from z ≤ x by transitivity z ≤ y ≤ x)
  have hxz : z ≤ x := E213.Meta.Int213.Order.le_trans hyz hxy
  have h_xz : (0 : Int) ≤ x - z := sub_nonneg_of_le' hxz
  have h_yz : (0 : Int) ≤ y - z := sub_nonneg_of_le' hyz
  have h_y  : (0 : Int) ≤ y := E213.Meta.Int213.Order.le_trans hz hyz
  -- first summand: (x−y)² · ((x−z) + y) ≥ 0
  have h1 : (0 : Int) ≤ (x-y)*(x-y)*((x-z) + y) :=
    mul_nonneg (sq_nonneg (x-y)) (add_nonneg h_xz h_y)
  -- second summand: z · ((x−z)(y−z)) ≥ 0
  have h2 : (0 : Int) ≤ z*((x-z)*(y-z)) :=
    mul_nonneg hz (mul_nonneg h_xz h_yz)
  exact add_nonneg h1 h2

/-! ## t = 2 -/

/-- ★★ **Schur's inequality, t = 2**, over `Int`.
    For `z ≤ y ≤ x` and `0 ≤ z`:
    `x²(x−y)(x−z) + y²(y−x)(y−z) + z²(z−x)(z−y) ≥ 0`.

    Split: `(x−y)²·P + z²·(x−z)(y−z)` with `P = x² + (x+y)(y−z) ≥ 0`. -/
theorem schur_t2 {x y z : Int} (hxy : y ≤ x) (hyz : z ≤ y) (hz : 0 ≤ z) :
    (0 : Int) ≤ x*x*(x-y)*(x-z) + y*y*(y-x)*(y-z) + z*z*(z-x)*(z-y) := by
  -- key regrouping identity into the two-summand SOS-style form
  have hid :
      x*x*(x-y)*(x-z) + y*y*(y-x)*(y-z) + z*z*(z-x)*(z-y)
        = (x-y)*(x-y)*(x*x + (x+y)*(y-z)) + z*z*((x-z)*(y-z)) := by ring_intZ
  rw [hid]
  have hxz : z ≤ x := E213.Meta.Int213.Order.le_trans hyz hxy
  have h_xz : (0 : Int) ≤ x - z := sub_nonneg_of_le' hxz
  have h_yz : (0 : Int) ≤ y - z := sub_nonneg_of_le' hyz
  have h_y  : (0 : Int) ≤ y := E213.Meta.Int213.Order.le_trans hz hyz
  have h_x  : (0 : Int) ≤ x := E213.Meta.Int213.Order.le_trans hz hxz
  -- P = x² + (x+y)(y−z) ≥ 0
  have hP : (0 : Int) ≤ x*x + (x+y)*(y-z) :=
    add_nonneg (sq_nonneg x) (mul_nonneg (add_nonneg h_x h_y) h_yz)
  -- first summand: (x−y)² · P ≥ 0
  have h1 : (0 : Int) ≤ (x-y)*(x-y)*(x*x + (x+y)*(y-z)) :=
    mul_nonneg (sq_nonneg (x-y)) hP
  -- second summand: z² · ((x−z)(y−z)) ≥ 0
  have h2 : (0 : Int) ≤ z*z*((x-z)*(y-z)) :=
    mul_nonneg (sq_nonneg z) (mul_nonneg h_xz h_yz)
  exact add_nonneg h1 h2

/-! ## Concrete smoke checks (closed numeric goals, `decide`) -/

-- t = 1 regrouping identity, numeric instance (5,3,2)
example :
    (5:Int)*(5-3)*(5-2) + 3*(3-5)*(3-2) + 2*(2-5)*(2-3)
      = (5-3)*(5-3)*((5-2) + 3) + 2*((5-2)*(3-2)) := by decide

-- t = 2 regrouping identity, numeric instance (7,4,1)
example :
    (7:Int)*7*(7-4)*(7-1) + 4*4*(4-7)*(4-1) + 1*1*(1-7)*(1-4)
      = (7-4)*(7-4)*(7*7 + (7+4)*(4-1)) + 1*1*((7-1)*(4-1)) := by decide

-- t = 1 nonneg, ordered triples
example : (0:Int) ≤ (4:Int)*(4-2)*(4-0) + 2*(2-4)*(2-0) + 0*(0-4)*(0-2) := by decide
example : (0:Int) ≤ (9:Int)*(9-5)*(9-3) + 5*(5-9)*(5-3) + 3*(3-9)*(3-5) := by decide
example : (0:Int) ≤ (6:Int)*(6-6)*(6-6) + 6*(6-6)*(6-6) + 6*(6-6)*(6-6) := by decide

-- t = 2 nonneg, ordered triples
example : (0:Int) ≤ (4:Int)*4*(4-2)*(4-0) + 2*2*(2-4)*(2-0) + 0*0*(0-4)*(0-2) := by decide
example : (0:Int) ≤ (9:Int)*9*(9-5)*(9-3) + 5*5*(5-9)*(5-3) + 3*3*(3-9)*(3-5) := by decide
example : (0:Int) ≤ (8:Int)*8*(8-8)*(8-1) + 8*8*(8-8)*(8-1) + 1*1*(1-8)*(1-8) := by decide

end E213.Lib.Math.Foundations.SchurInequality
