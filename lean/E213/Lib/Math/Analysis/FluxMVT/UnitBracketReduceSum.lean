import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumDetermined
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
/-!
# cutSumAux reduce template — G110 FLUX-1 sum companion

Parallel to `UnitBracketReduce.cutMulOuter_unitBracket_reduce_at`,
this template extracts the recurring `cutSumAux_congr` step that
appears in derivative-witness proofs (e.g.,
`squareDerivative_at_half_at`, `mid_witness_propagates_at`).

`cutSumAux_unitBracket_reduce_at` packages the `cutSumAux_congr`
invocation with the canonical full-bound (m1Max ≤ m1Max via Nat.le_refl).
Caller supplies the per-instance pointwise reductions `hL` and `hR`;
then a short `rw` finishes the proof.
-/

namespace E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum

open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSumAux)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumDetermined (cutSumAux_congr)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- ★ Generic ∅-axiom reduction: rewrite
    `cutSumAux f g k bound bound` to
    `cutSumAux gL gR k bound bound`
    using `cutSumAux_congr` + pointwise reductions.  PURE.

    Targets `gL` and `gR` are arbitrary cuts (the caller specifies
    them), giving full flexibility for the different reductions
    (constCut s d for any s, d; cutMul of constCuts; etc.). -/
theorem cutSumAux_unitBracket_reduce_at
    (f g gL gR : Nat → Nat → Bool) (k bound : Nat)
    (hL : ∀ m', m' ≤ bound → f m' (2*k) = gL m' (2*k))
    (hR : ∀ m', m' ≤ bound → g m' (2*k) = gR m' (2*k)) :
    cutSumAux f g k bound bound = cutSumAux gL gR k bound bound :=
  cutSumAux_congr k bound f gL g gR hL hR bound (Nat.le_refl _)

end E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum
