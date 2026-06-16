import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic

/-!
# Muirhead's inequality `[2,1,0] ≻ [1,1,1]` over `Int` (∅-axiom)

  * ★★★ `muirhead_210_111` — for `0 ≤ a,b,c`,
      `6abc ≤ Σ_sym a²b`, i.e.
      `6*a*b*c ≤ a*a*b + a*a*c + b*b*a + b*b*c + c*c*a + c*c*b`.
    SOS identity: `(Σ_sym a²b) − 6abc
                    = a*(b−c)*(b−c) + b*(c−a)*(c−a) + c*(a−b)*(a−b)`.
    Each summand `≥ 0` (nonneg variable × a square), so the difference `≥ 0`.

Companion: the `[3,0,0] ≻ [1,1,1]` case `3abc ≤ a³+b³+c³` is already proved in
`Lib/Math/Foundations/SumCubesAMGM.lean` (`amgm3`); not reproved here.

All ∅-axiom (reuses `E213.Meta.Int213` PURE order primitives, same skeleton as
`NesbittInequality.am_hm_core` / `SchurInequality`).
-/

namespace E213.Lib.Math.Foundations.MuirheadInequality

open E213.Meta.Int213

/-- ★★★ **Muirhead `[2,1,0] ≻ [1,1,1]`** (ℤ): for `0 ≤ a,b,c`,
    `6abc ≤ a²b + a²c + b²a + b²c + c²a + c²b`. -/
theorem muirhead_210_111 {a b c : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    6*a*b*c
      ≤ a*a*b + a*a*c + b*b*a + b*b*c + c*c*a + c*c*b := by
  -- SOS identity for the difference: Σ_sym a²b − 6abc
  --   = a(b−c)² + b(c−a)² + c(a−b)²
  have hid :
      (a*a*b + a*a*c + b*b*a + b*b*c + c*c*a + c*c*b) - 6*a*b*c
        = a*((b-c)*(b-c)) + (b*((c-a)*(c-a)) + c*((a-b)*(a-b))) := by
    ring_intZ
  -- each summand nonneg: nonneg var times a square
  have h1 : 0 ≤ a*((b-c)*(b-c)) := mul_nonneg ha (int_sq_nonneg (b-c))
  have h2 : 0 ≤ b*((c-a)*(c-a)) := mul_nonneg hb (int_sq_nonneg (c-a))
  have h3 : 0 ≤ c*((a-b)*(a-b)) := mul_nonneg hc (int_sq_nonneg (a-b))
  have hpos :
      0 ≤ (a*a*b + a*a*c + b*b*a + b*b*c + c*c*a + c*c*b) - 6*a*b*c := by
    rw [hid]; exact add_nonneg h1 (add_nonneg h2 h3)
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hpos)

/-! ### Concrete smokes (closed terms, `decide`). Equality at `a=b=c`. -/

example : 6*(1:Int)*1*1 ≤ 1*1*1 + 1*1*1 + 1*1*1 + 1*1*1 + 1*1*1 + 1*1*1 := by decide
example : 6*(2:Int)*2*2 ≤ 2*2*2 + 2*2*2 + 2*2*2 + 2*2*2 + 2*2*2 + 2*2*2 := by decide
example : 6*(1:Int)*2*3
    ≤ 1*1*2 + 1*1*3 + 2*2*1 + 2*2*3 + 3*3*1 + 3*3*2 := by decide
example : 6*(0:Int)*5*7
    ≤ 0*0*5 + 0*0*7 + 5*5*0 + 5*5*7 + 7*7*0 + 7*7*5 := by decide

end E213.Lib.Math.Foundations.MuirheadInequality
