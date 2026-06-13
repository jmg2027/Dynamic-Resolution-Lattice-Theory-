import E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCut
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulN
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulConstConst
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul

/-!
# NValidCutMul — bundled `ValidCutN N` multiplication to N²-fiber

The `ValidCutN N` framework's bundled addition `addN` lifts
`cutSumN N` from cut-level to the bundled structure, with the
`represents` field carrying the algebraic numerator.  This file
delivers the analogous bundled product:

  `mulN (N : Nat) (hN : 0 < N) (va vc : ValidCutN N) : ValidCutN (N * N)`

Maps `(a / N) · (c / N) → (a · c) / N²` at the bundled level by
using the canonical `constCut (a · c) (N · N)` as the cut field
directly (rather than going through `cutMulN N`'s search, which
has the same precision artifact as standard `cutMul`).  The
algebraic numerator `a · c` is the product of the input
`represents` fields, and the `is_at_denom` witness is
reflexivity since the cut is by construction `constCut`-shape.

The forward link to `cutMulN N` is `cutMulN_const_const_forward`
(`Mul/CutMulN.lean`): whenever `cutMulN N` certifies a product
witness at `(m, k)`, the bundled product's `cut` agrees there.
The backward link fails at the cut level (precision artifact);
the bundled structure circumvents this by recording the
algebraic numerator directly.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.NumberSystems.Real213.NValidCutMul

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq cutEq_refl)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.NValidCut (ValidCutN ofValidCutN)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMulN
  (cutMulN cutMulN_const_const_forward)

/-! ## §1 — Bundled product to N²-fiber -/

/-- ★★★★★ **Bundled product** `(a / N) · (c / N) = (a · c) / N²`
    at the `ValidCutN` level.  Maps `ValidCutN N × ValidCutN N
    → ValidCutN (N · N)`.  The cut field is the canonical
    `constCut`; algebraic numerator is the product of inputs'
    represents.  `is_at_denom` witness is `cutEq_refl`. -/
def mulN (N : Nat) (_hN : 0 < N) (va vc : ValidCutN N) :
    ValidCutN (N * N) where
  cut := constCut (va.represents * vc.represents) (N * N)
  represents := va.represents * vc.represents
  is_at_denom := cutEq_refl _

/-- The bundled product's `represents` field is the product of
    the inputs' represents.  By definition. -/
theorem mulN_represents (N : Nat) (hN : 0 < N) (va vc : ValidCutN N) :
    (mulN N hN va vc).represents = va.represents * vc.represents := rfl

/-- The bundled product's `cut` field is the canonical N²-fiber
    constCut at the product numerator.  By definition. -/
theorem mulN_cut (N : Nat) (hN : 0 < N) (va vc : ValidCutN N) :
    (mulN N hN va vc).cut
      = constCut (va.represents * vc.represents) (N * N) := rfl

/-! ## §2 — Commutativity at the bundled level -/

/-- ★★ **Bundled product commutativity**: `mulN N va vc` and
    `mulN N vc va` agree on their cut fields up to `cutEq`.
    Reduces via `mulN_cut` + `Nat.mul_comm` on the represents. -/
theorem mulN_comm (N : Nat) (hN : 0 < N) (va vc : ValidCutN N) :
    cutEq (mulN N hN va vc).cut (mulN N hN vc va).cut := by
  rw [mulN_cut, mulN_cut, Nat.mul_comm vc.represents va.represents]
  exact cutEq_refl _

/-! ## §3 — Associativity to N⁴-fiber

Bundled associativity carries types through:
  `(va · vc) · ve : ValidCutN (N * N * N * N)`
  `va · (vc · ve) : ValidCutN (N * (N * N) * ?)` — type-level
  hierarchy.  For uniformity we re-bundle to a single N²-fiber
  product framework when working within a fixed denominator
  tier.  The cleanest associativity is at the *represents* level:
  `va.r · vc.r · ve.r` reassociates by `Nat.mul_assoc`. -/

/-- ★★★ **Represents-level associativity**: the bundled
    product's numerator field reassociates per `Nat.mul_assoc`. -/
theorem mulN_represents_assoc
    (N : Nat) (hN : 0 < N) (va vc ve : ValidCutN N) :
    va.represents * vc.represents * ve.represents
      = va.represents * (vc.represents * ve.represents) :=
  E213.Tactic.NatHelper.mul_assoc _ _ _

end E213.Lib.Math.NumberSystems.Real213.NValidCutMul
