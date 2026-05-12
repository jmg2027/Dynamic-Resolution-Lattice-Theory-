import E213.Lib.Math.CayleyDickson.Sedenion
import E213.Lib.Math.CayleyDickson.LipschitzAlgebra213
import E213.Lib.Math.NatHelpers.IntHelpers
import E213.Lib.Math.CayleyDickson.CayleyHeavy
import E213.Lib.Math.Tactic.HurwitzRing
import E213.Theory.Internal.Algebra213

/-!
# Sedenion "heavy" identities

`conj_conj` migrated to ∅-axiom via Ring213.neg_neg cascade.
`flexible` / `conj_mul_anti` still use hurwitz_ring (DIRTY) — would
need Cayley alternative ring algebra to avoid Int polynomial.
-/

namespace E213.Lib.Math.CayleyDickson.SedenionHeavy


open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Lib.Math.CayleyDickson.Sedenion
open E213.Lib.Math.CayleyDickson.Sedenion.Sedenion
open E213.Lib.Math.CayleyDickson.CayleyHeavy
open E213.Theory.Internal.Algebra213
open E213.Tactic E213.Lib.Math.CayleyDickson.Cayley E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

/-- ∅-axiom Cayley `neg_neg` via Lipschitz Ring213 projection. -/
private theorem cayley_neg_neg (u : E213.Lib.Math.CayleyDickson.Cayley.Cayley) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Cayley.Cayley.ext
  · show -(-u.re) = u.re; exact Ring213.neg_neg u.re
  · show -(-u.im) = u.im; exact Ring213.neg_neg u.im

/-- ★ ∅-axiom Sedenion conjugation involutive via Cayley cascade. -/
theorem conj_conj (u : Sedenion) : conj (conj u) = u := by
  apply Sedenion.ext
  · show u.re.conj.conj = u.re
    exact E213.Lib.Math.CayleyDickson.Cayley.conj_conj u.re
  · show -(-u.im) = u.im
    exact cayley_neg_neg u.im

open E213.Tactic

set_option maxHeartbeats 8000000 in
/-- **Sedenion flexibility** — DIRTY (32 Int vars). -/
theorem flexible (a b : Sedenion) : (a * b) * a = a * (b * a) := by
  hurwitz_ring

set_option maxHeartbeats 8000000 in
/-- **Sedenion anti-distributivity of conj** — DIRTY (32 Int vars). -/
theorem conj_mul_anti (u v : Sedenion) :
    conj (u * v) = conj v * conj u := by
  hurwitz_ring

open E213.Lib.Math.CayleyDickson.Cayley E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

def normSq (u : Sedenion) : Int :=
  E213.Lib.Math.CayleyDickson.CayleyHeavy.normSq u.re
    + E213.Lib.Math.CayleyDickson.CayleyHeavy.normSq u.im

theorem normSq_zd_left_ne_zero : normSq zd_left ≠ 0 := by decide
theorem normSq_zd_right_ne_zero : normSq zd_right ≠ 0 := by decide

theorem normSq_zero : normSq (0 : Sedenion) = 0 := by
  show E213.Lib.Math.CayleyDickson.CayleyHeavy.normSq (0 : Cayley)
       + E213.Lib.Math.CayleyDickson.CayleyHeavy.normSq (0 : Cayley) = 0
  decide

/-- Norm multiplicativity FAILS at Sedenion (witnesses zero divisors). -/
theorem normSq_mul_fails :
    ∃ u v : Sedenion, normSq (u * v) ≠ normSq u * normSq v := by
  refine ⟨zd_left, zd_right, ?_⟩
  rw [zd_product_zero, normSq_zero]
  decide

end E213.Lib.Math.CayleyDickson.SedenionHeavy
