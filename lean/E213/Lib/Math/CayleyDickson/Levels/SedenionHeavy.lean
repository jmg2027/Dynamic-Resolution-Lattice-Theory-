import E213.Lib.Math.CayleyDickson.Levels.Sedenion
import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzAlgebra213
import E213.Meta.Nat.IntHelpers
import E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy
import E213.Lib.Math.Tactic.HurwitzRing
import E213.Meta.Algebra213.Core

/-!
# Sedenion "heavy" identities

`conj_conj` migrated to ∅-axiom via Ring213.neg_neg cascade.
`flexible` / `conj_mul_anti` still use hurwitz_ring (DIRTY) — would
need Cayley alternative ring algebra to avoid Int polynomial.
-/

namespace E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy


open E213.Lib.Math.CayleyDickson.Integer.ZI
open E213.Lib.Math.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.CayleyDickson.Levels.Sedenion.Sedenion
open E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy
open E213.Meta.Algebra213
open E213.Tactic E213.Lib.Math.CayleyDickson.Levels.Cayley E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz

/-- ∅-axiom Cayley `neg_neg` via Lipschitz Ring213 projection. -/
private theorem cayley_neg_neg (u : E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley.ext
  · show -(-u.re) = u.re; exact Ring213.neg_neg u.re
  · show -(-u.im) = u.im; exact Ring213.neg_neg u.im

/-- ★ ∅-axiom Sedenion conjugation involutive via Cayley cascade. -/
theorem conj_conj (u : Sedenion) : conj (conj u) = u := by
  apply Sedenion.ext
  · show u.re.conj.conj = u.re
    exact E213.Lib.Math.CayleyDickson.Levels.Cayley.conj_conj u.re
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

open E213.Lib.Math.CayleyDickson.Levels.Cayley E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz

def normSq (u : Sedenion) : Int :=
  E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq u.re
    + E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq u.im

theorem normSq_zd_left_ne_zero : normSq zd_left ≠ 0 := by decide
theorem normSq_zd_right_ne_zero : normSq zd_right ≠ 0 := by decide

theorem normSq_zero : normSq (0 : Sedenion) = 0 := by
  show E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq (0 : Cayley)
       + E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq (0 : Cayley) = 0
  decide

/-- Norm multiplicativity FAILS at Sedenion (witnesses zero divisors). -/
theorem normSq_mul_fails :
    ∃ u v : Sedenion, normSq (u * v) ≠ normSq u * normSq v := by
  refine ⟨zd_left, zd_right, ?_⟩
  rw [zd_product_zero, normSq_zero]
  decide

end E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy
