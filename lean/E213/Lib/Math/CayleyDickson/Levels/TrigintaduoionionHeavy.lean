import E213.Lib.Math.CayleyDickson.Levels.Trigintaduonion
import E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy
import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzAlgebra213
import E213.Lib.Math.Tactic.HurwitzRing
import E213.Meta.Algebra213.Core

/-!
# Trigintaduonion "heavy" identities

`conj_conj` migrated to ∅-axiom via Ring213.neg_neg cascade
(Lipschitz Ring213 instance + componentwise structural
recursion through Cayley → Sedenion → Trigintaduonion).

`conj_mul_anti` still uses hurwitz_ring (DIRTY) — 128-Int-var
2-factor polynomial.
-/

namespace E213.Lib.Math.CayleyDickson.Levels.TrigintaduoionionHeavy


open E213.Lib.Math.CayleyDickson.Integer.ZI
open E213.Lib.Math.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.CayleyDickson.Levels.Trigintaduonion
open E213.Lib.Math.CayleyDickson.Levels.Trigintaduonion.Trigintaduonion
open E213.Lib.Math.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.CayleyDickson.Levels.Sedenion.Sedenion
open E213.Lib.Math.CayleyDickson.Levels.Cayley
open E213.Lib.Math.CayleyDickson.Tower.CDDouble
open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Meta.Algebra213
open E213.Tactic

/-- ∅-axiom Cayley `neg_neg` via Lipschitz Ring213. -/
private theorem cayley_neg_neg (u : E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley.ext
  · show -(-u.re) = u.re; exact Ring213.neg_neg u.re
  · show -(-u.im) = u.im; exact Ring213.neg_neg u.im

/-- ∅-axiom Sedenion `neg_neg` via Cayley. -/
private theorem sedenion_neg_neg
    (u : E213.Lib.Math.CayleyDickson.Levels.Sedenion.Sedenion) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Levels.Sedenion.Sedenion.ext
  · show -(-u.re) = u.re; exact cayley_neg_neg u.re
  · show -(-u.im) = u.im; exact cayley_neg_neg u.im

/-- ★ ∅-axiom Trigintaduonion conjugation involutive via Sedenion cascade. -/
theorem conj_conj (u : Trigintaduonion) : conj (conj u) = u := by
  apply Trigintaduonion.ext
  · show u.re.conj.conj = u.re
    exact E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy.conj_conj u.re
  · show -(-u.im) = u.im
    exact sedenion_neg_neg u.im

set_option maxHeartbeats 32000000 in
/-- Anti-distributivity at layer 4 — DIRTY (128 Int vars). -/
theorem conj_mul_anti (u v : Trigintaduonion) :
    conj (u * v) = conj v * conj u := by
  hurwitz_ring

end E213.Lib.Math.CayleyDickson.Levels.TrigintaduoionionHeavy
