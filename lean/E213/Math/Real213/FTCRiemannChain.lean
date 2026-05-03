import E213.Math.Real213.FTCRiemannGeneric
import E213.Math.Real213.MVTWitnessChain

/-!
# Research.Real213FTCRiemannChain

Phase CD: applying generic FTC-Riemann to chain-rule constructions.

For id ∘ x² (= x² as function, but built via composeIsDifferentiable):
witness c = 1/2, passthrough endpoints, hence FTC-Riemann at depth 0
follows automatically from the generic theorem.
-/

namespace E213.Math.Real213.FTCRiemannChain

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable composeIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.MVTWitnessChain.HasDyadicMVTWitness (id_compose_square)
open E213.Math.Real213.FluxMVTMore.HasDyadicMVTWitness (mid_id_square)
open E213.Math.Real213.FTCRiemannGeneric
  (ftc_riemann_generic_via_witness ftc_riemann_generic_for_square)
open E213.Math.Real213.CutMulOne (cutMul_one_one)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut)

end E213.Math.Real213.FTCRiemannChain
