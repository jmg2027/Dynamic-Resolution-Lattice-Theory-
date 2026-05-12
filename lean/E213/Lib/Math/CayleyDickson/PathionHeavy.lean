import E213.Lib.Math.CayleyDickson.Pathion
import E213.Lib.Math.CayleyDickson.TrigintaduoionionHeavy
import E213.Lib.Math.CayleyDickson.LipschitzAlgebra213
import E213.Lib.Math.Tactic.HurwitzRing
import E213.Meta.Algebra213.Core

/-!
# Pathion "heavy" identities — ∅-axiom via Ring213 cascade

`conj_conj` at CD layer 5 (128 Int coords) — migrated to PURE
via structural recursion through Cayley→Sedenion→Trigintaduonion→Pathion
neg_neg cascades, each hop via Lipschitz Ring213.neg_neg.
-/

namespace E213.Lib.Math.CayleyDickson.PathionHeavy


open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Lib.Math.CayleyDickson.Pathion
open E213.Lib.Math.CayleyDickson.Pathion.Pathion
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

/-- ∅-axiom Sedenion `neg_neg`. -/
private theorem sedenion_neg_neg
    (u : E213.Lib.Math.CayleyDickson.Sedenion.Sedenion) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Sedenion.Sedenion.ext
  · show -(-u.re) = u.re; exact cayley_neg_neg u.re
  · show -(-u.im) = u.im; exact cayley_neg_neg u.im

/-- ∅-axiom Trigintaduonion `neg_neg`. -/
private theorem trigintaduonion_neg_neg (u : Trigintaduonion) :
    -(-u) = u := by
  apply Trigintaduonion.ext
  · show -(-u.re) = u.re; exact sedenion_neg_neg u.re
  · show -(-u.im) = u.im; exact sedenion_neg_neg u.im

/-- ★ ∅-axiom Pathion conjugation involutive — CD layer 5, 128 Int vars. -/
theorem conj_conj (u : Pathion) : conj (conj u) = u := by
  apply Pathion.ext
  · show u.re.conj.conj = u.re
    exact E213.Lib.Math.CayleyDickson.TrigintaduoionionHeavy.conj_conj u.re
  · show -(-u.im) = u.im
    exact trigintaduonion_neg_neg u.im

end E213.Lib.Math.CayleyDickson.PathionHeavy
