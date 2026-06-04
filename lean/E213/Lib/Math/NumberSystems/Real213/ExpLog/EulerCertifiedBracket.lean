import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut

/-!
# EulerCertifiedBracket — e's certified modulus on its proven bracket (witness form)

This file records the *witness* form of e's cut-Cauchy certificate: wherever a strict
rational bracket for e is proven, the convergence modulus is the witness index, via
the constructive `MonotonicBounded.orderCauchy_from_{true_forever, false_witness}`.
On e's proven decided region `e ∈ (8/3, 3)`:

  * `euler_certified_at_3`   — `e < 3`: true at every layer, modulus `0`;
  * `euler_certified_at_8_3` — `e > 8/3`: false from layer `4`, modulus `4`.

These are the bracket endpoints made into moduli directly from the proven bounds.

The *total* per-`(m,k)` modulus for e (`N(m,k) = k+2`, every cut, ∅-axiom) lives in
`EulerModulus` (`euler_total_modulus` / `eHolonomicReal`); it uses e's factorial-tail
rate rather than a per-`(m,k)` bracket witness.  This file is the elementary,
bound-driven view of the same Cauchy property.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCertifiedBracket

open E213.Lib.Math.Cauchy.Archimedean (orderProj)
open E213.Lib.Math.Cauchy.MonotonicBounded
  (orderCauchy_from_true_forever orderCauchy_from_false_witness)
open E213.Lib.Math.Cauchy.EulerSeq (eulerRawSeq euler_isAbMonotonic euler_isAbPositiveB)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCut (eulerCut_at_3 eulerCut_below_8_3)
open E213.Lens.Instances.AB (abLens)

/-- ★★ **e's cut is certified-Cauchy at `3/1` with modulus `0`.**  `e < 3` holds at
    every convergent layer (`eulerCut_at_3` — true forever), so the cut value is
    constant from the start: the constructive (true-forever) branch of
    `MonotonicBounded`. -/
theorem euler_certified_at_3 :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      orderProj 3 1 (abLens.view (eulerRawSeq i))
        = orderProj 3 1 (abLens.view (eulerRawSeq j)) :=
  orderCauchy_from_true_forever eulerRawSeq 3 1 eulerCut_at_3

set_option maxRecDepth 8000 in
/-- ★★ **e's cut is certified-Cauchy at `8/3` with modulus `4`.**  `e > 8/3` from
    layer 4 (`eulerCut_below_8_3` — false witness at `N₀ = 4`), and the monotone
    chain propagates `false` upward: the constructive (false-witness) branch. -/
theorem euler_certified_at_8_3 :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      orderProj 8 3 (abLens.view (eulerRawSeq i))
        = orderProj 8 3 (abLens.view (eulerRawSeq j)) :=
  orderCauchy_from_false_witness eulerRawSeq euler_isAbMonotonic euler_isAbPositiveB
    8 3 4 (eulerCut_below_8_3 4 (Nat.le_refl 4))

/-- ★★★ **e is certified-Cauchy on its whole proven bracket `(8/3, 3)`.**  Both
    boundary cuts have an explicit ∅-axiom modulus — the `HolonomicReal` generator
    certifies e on its decided region.  The total modulus (every `m/k`, including the
    undecided rationals approaching e) is the open irrationality-measure core (file
    header). -/
theorem euler_certified_bracket :
    (∃ N, ∀ i j, i ≥ N → j ≥ N →
        orderProj 3 1 (abLens.view (eulerRawSeq i))
          = orderProj 3 1 (abLens.view (eulerRawSeq j)))
    ∧ (∃ N, ∀ i j, i ≥ N → j ≥ N →
        orderProj 8 3 (abLens.view (eulerRawSeq i))
          = orderProj 8 3 (abLens.view (eulerRawSeq j))) :=
  ⟨euler_certified_at_3, euler_certified_at_8_3⟩

end E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerCertifiedBracket
