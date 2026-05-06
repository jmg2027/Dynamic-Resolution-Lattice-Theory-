import E213.Math.CayleyDickson.Sedenion
import E213.Math.NatHelpers.IntHelpers
import E213.Math.CayleyDickson.CayleyHeavy
import E213.Math.Tactic.HurwitzRing

/-!
# Sedenion "heavy" identities — observing tactic limits

At 16 coords per sedenion, 2-variable identities have
32 Int coordinates, 3-variable identities 48 coordinates.
This file explores which polynomial identities `hurwitz_ring`
can still close at layer 3.
-/

namespace E213.Math.CayleyDickson.SedenionHeavy


open E213.Math.CayleyDickson.ZI
open E213.Math.CayleyDickson.ZI.ZI
open E213.Tactic E213.Math.CayleyDickson.Cayley E213.Math.CayleyDickson.CDDouble.Lipschitz

set_option maxHeartbeats 2000000 in
/-- **Sedenion conjugation is involutive**: 1-variable
    identity, 16 Int coordinates. -/
theorem conj_conj (u : Sedenion) : conj (conj u) = u := by
  hurwitz_ring

open E213.Tactic

set_option maxHeartbeats 8000000 in
/-- **Sedenion flexibility** `(a·b)·a = a·(b·a)`.  Classically
    holds — sedenions ARE flexible (one of the axioms that
    survives past octonion alternativity loss).  32 Int vars;
    3-factor polynomial; stress test for `hurwitz_ring`. -/
theorem flexible (a b : Sedenion) : (a * b) * a = a * (b * a) := by
  hurwitz_ring

open E213.Tactic

set_option maxHeartbeats 8000000 in
/-- **Sedenion anti-distributivity of conj**: `conj(u·v) =
    conj(v) · conj(u)`.  CD signature — same as Lipschitz
    and Cayley.  32 Int vars, 2-factor polynomial. -/
theorem conj_mul_anti (u v : Sedenion) :
    conj (u * v) = conj v * conj u := by
  hurwitz_ring

open E213.Math.CayleyDickson.Cayley E213.Math.CayleyDickson.CDDouble.Lipschitz

/-- Sedenion norm-squared: `re.normSq + im.normSq` at
    Cayley level. -/
def normSq (u : Sedenion) : Int :=
  Cayley.normSq u.re + Cayley.normSq u.im

/-- `|zd_left|²` is nonzero. -/
theorem normSq_zd_left_ne_zero : normSq zd_left ≠ 0 := by decide

/-- `|zd_right|²` is nonzero. -/
theorem normSq_zd_right_ne_zero : normSq zd_right ≠ 0 := by decide

/-- `normSq (0 : Sedenion) = 0`. -/
theorem normSq_zero : normSq (0 : Sedenion) = 0 := by
  show Cayley.normSq (0 : Cayley) + Cayley.normSq (0 : Cayley) = 0
  decide

/-- **Norm multiplicativity FAILS at Sedenion.**
    `zd_left · zd_right = 0` so `|zd_left · zd_right|² = 0`,
    but `|zd_left|² · |zd_right|²` is positive.  Concrete
    witness that Sedenion is NOT a composition algebra. -/
theorem normSq_mul_fails :
    ∃ u v : Sedenion, normSq (u * v) ≠ normSq u * normSq v := by
  refine ⟨zd_left, zd_right, ?_⟩
  rw [zd_product_zero, normSq_zero]
  decide

end E213.Math.CayleyDickson.SedenionHeavy
