import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic

/-!
# Heron's formula — algebraic core over `Int` (∅-axiom)

The factored form `16·Area²` (`s = (a+b+c)/2`,
`16·Area² = (a+b+c)(−a+b+c)(a−b+c)(a+b−c)`) equals the symmetric polynomial
`2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴`.  (The `s`-form `16·s(s−a)(s−b)(s−c)` is the
same identity with `2s=a+b+c`.)  All `*` explicit (`ring_intZ` treats `^` as an atom).

  * ★★★ `heron_identity` — the factored `16·Area²` = symmetric polynomial.
  * ★★ `heron_pythagorean` — `a²+b²=c² ⇒ 16·Area² = 4a²b²` (so `Area = ab/2`).

All ∅-axiom (pure `ring_intZ`).
-/

namespace E213.Lib.Math.Foundations.HeronFormula

/-- ★★★ **Heron's identity**: `16·Area² = (a+b+c)(−a+b+c)(a−b+c)(a+b−c)` equals the
    symmetric polynomial `2a²b²+2b²c²+2c²a²−a⁴−b⁴−c⁴`. -/
theorem heron_identity (a b c : Int) :
    (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c)
      = 2*a*a*b*b + 2*b*b*c*c + 2*c*c*a*a - a*a*a*a - b*b*b*b - c*c*c*c := by
  ring_intZ

/-- ★★ **Pythagorean special case**: if `a² + b² = c²` (right triangle, `c` the
    hypotenuse), then `16·Area² = 4a²b²` (so `Area = ab/2`). -/
theorem heron_pythagorean (a b c : Int) (h : a*a + b*b = c*c) :
    (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c) = 4*a*a*b*b := by
  rw [heron_identity]
  have hc : c*c = a*a + b*b := h.symm
  rw [show c*c*c*c = (c*c)*(c*c) from by ring_intZ,
      show 2*b*b*c*c = 2*b*b*(c*c) from by ring_intZ,
      show 2*c*c*a*a = 2*(c*c)*a*a from by ring_intZ,
      hc]
  ring_intZ

/-- Numeric smoke: (3,4,5) right triangle, Area = 6, `16·Area² = 576`. -/
theorem heron_smoke :
    (3+4+5)*(-3+4+5)*(3-4+5)*(3+4-5) = (576 : Int)
    ∧ 4*3*3*4*4 = (576 : Int) := by decide

end E213.Lib.Math.Foundations.HeronFormula
