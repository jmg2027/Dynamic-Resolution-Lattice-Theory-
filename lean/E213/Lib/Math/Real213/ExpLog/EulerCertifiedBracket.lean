import E213.Lib.Math.Real213.ExpLog.EulerCut

/-!
# EulerCertifiedBracket — e's certified modulus on its decided region (the generator's
  constructive boundary)

`HolonomicReal` (autonomous/φ case) carries its convergence modulus as a *constructed
field*: φ — an algebraic (det-1, order-2 constant-coefficient) real — has a **total**
modulus `N(m,k) = 2k`, proven ∅-axiom.  The natural next rung, deriving a modulus from
a *transcendental's* recurrence (e, coefficient `n+1`), runs into a sharp obstruction,
and this file pins exactly where.

**The wall.**  `MonotonicBounded` proves: monotone-bounded ⟹ Cauchy *only* with LEM —
the total `∀(m,k), ∃N` closure needs the case split "`orderProj` true for all `n`" vs
"false at some `n`", i.e. **deciding `e` against `m/k`**.  For a transcendental `e`
this is a *constructive irrationality measure* (a computable lower bound on
`|e − m/k|`), which is not available ∅-axiom.  So e has **no total ∅-axiom modulus**
— the `HolonomicReal` generator is constructive on the algebraic (autonomous) class
and stops at the transcendental boundary.

**What is constructive.**  Wherever a strict rational *bracket* is provable, the
modulus is the witness index (`MonotonicBounded.orderCauchy_from_{true_forever,
false_witness}`).  e's convergent cut-sequence is therefore certified-Cauchy on its
proven decided region `e ∈ (8/3, 3)`:

  * `euler_certified_at_3`   — `e < 3`: true at every layer, modulus `0`;
  * `euler_certified_at_8_3` — `e > 8/3`: false from layer `4`, modulus `4`.

So the generator *does* certify e at every `(m,k)` the bounds decide; only the
undecided boundary (rationals approaching e) is the open irrationality-measure core.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.ExpLog.EulerCertifiedBracket

open E213.Lib.Math.Cauchy.Archimedean (orderProj)
open E213.Lib.Math.Cauchy.MonotonicBounded
  (orderCauchy_from_true_forever orderCauchy_from_false_witness)
open E213.Lib.Math.Cauchy.EulerSeq (eulerRawSeq euler_isAbMonotonic euler_isAbPositiveB)
open E213.Lib.Math.Real213.ExpLog.EulerCut (eulerCut_at_3 eulerCut_below_8_3)
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

end E213.Lib.Math.Real213.ExpLog.EulerCertifiedBracket
