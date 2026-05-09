import E213.Lib.Math.CayleyDickson.Trigintaduonion
import E213.Lib.Math.CayleyDickson.SedenionHeavy
import E213.Lib.Math.CayleyDickson.LipschitzAlgebra213
import E213.Lib.Math.Tactic.HurwitzRing
import E213.Theory.Internal.Algebra213

/-!
# Trigintaduonion "heavy" identities

`conj_conj` migrated to ∅-axiom via Ring213.neg_neg cascade
(Lipschitz Ring213 instance + componentwise structural
recursion through Cayley → Sedenion → Trigintaduonion).

`conj_mul_anti` still uses hurwitz_ring (DIRTY) — 128-Int-var
2-factor polynomial.
-/

namespace E213.Lib.Math.CayleyDickson.TrigintaduoionionHeavy


open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Lib.Math.CayleyDickson.Trigintaduonion
open E213.Lib.Math.CayleyDickson.Trigintaduonion.Trigintaduonion
open E213.Lib.Math.CayleyDickson.Sedenion
open E213.Lib.Math.CayleyDickson.Sedenion.Sedenion
open E213.Lib.Math.CayleyDickson.Cayley
open E213.Lib.Math.CayleyDickson.CDDouble
open E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz
open E213.Theory.Internal.Algebra213
open E213.Tactic

/-- ∅-axiom Cayley `neg_neg` via Lipschitz Ring213. -/
private theorem cayley_neg_neg (u : E213.Lib.Math.CayleyDickson.Cayley.Cayley) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Cayley.Cayley.ext
  · show -(-u.re) = u.re; exact Ring213.neg_neg u.re
  · show -(-u.im) = u.im; exact Ring213.neg_neg u.im

/-- ∅-axiom Sedenion `neg_neg` via Cayley. -/
private theorem sedenion_neg_neg
    (u : E213.Lib.Math.CayleyDickson.Sedenion.Sedenion) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Sedenion.Sedenion.ext
  · show -(-u.re) = u.re; exact cayley_neg_neg u.re
  · show -(-u.im) = u.im; exact cayley_neg_neg u.im

/-- ★ ∅-axiom Trigintaduonion conjugation involutive via Sedenion cascade. -/
theorem conj_conj (u : Trigintaduonion) : conj (conj u) = u := by
  apply Trigintaduonion.ext
  · show u.re.conj.conj = u.re
    exact E213.Lib.Math.CayleyDickson.SedenionHeavy.conj_conj u.re
  · show -(-u.im) = u.im
    exact sedenion_neg_neg u.im

set_option maxHeartbeats 32000000 in
/-- Anti-distributivity at layer 4 — DIRTY (128 Int vars). -/
theorem conj_mul_anti (u v : Trigintaduonion) :
    conj (u * v) = conj v * conj u := by
  hurwitz_ring

end E213.Lib.Math.CayleyDickson.TrigintaduoionionHeavy
