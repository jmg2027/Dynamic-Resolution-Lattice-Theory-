import E213.Math.Real213.FTCRiemannSquare
import E213.Math.Real213.ClassicCalcMid

/-!
# Research.Real213FTCRiemannMid

Phase CB: FTC-Riemann for mid(x, x²) at unit, depth 0.

Same propEq pattern as x² extends to mid(x, x²) since both
have MVT witness c = 1/2 = unitBracket midpoint.
-/

namespace E213.Math.Real213.FTCRiemannMid

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.DyadicBracket.DyadicBracket (midCut)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Math.Real213.FTCRiemannSquare (unitBracket_midCut)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at cutMid_zero_zero_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut_at)
open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

/-! ### PURE pointwise variants (∅-axiom) -/

/-- ★ Riemann sum of mid(x, x²)' at unitBracket depth 0, pointwise (PURE). -/
theorem riemann_mid_id_square_derivative_zero_at (m k : Nat) :
    riemannSampleSum (midIsDifferentiable idIsDifferentiable
                       squareIsDifferentiable).derivative unitBracket 0 m k
      = constCut 1 1 m k :=
  mid_id_square_derivative_at_half_at m k


/-- ★ Phase CB capstone (PURE) — pointwise Riemann sum for mid(x, x²). -/
theorem ftc_riemann_mid_capstone_pure :
    ∀ m k, riemannSampleSum (midIsDifferentiable idIsDifferentiable
                              squareIsDifferentiable).derivative
             unitBracket 0 m k = constCut 1 1 m k :=
  riemann_mid_id_square_derivative_zero_at

end E213.Math.Real213.FTCRiemannMid
