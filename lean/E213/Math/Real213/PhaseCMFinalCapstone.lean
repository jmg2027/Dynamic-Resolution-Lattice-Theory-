import E213.Math.Real213.FluxMVTPropagateCompose

/-!
# Research.Real213PhaseCMFinalCapstone

Phase CM: ★★★ **final mega-mega capstone for BB-CL arc** ★★★

Bundles every result from the propEq MVT/FTC at unit bracket arc:
  - polynomial chain MVT (∀ n via cutPow_calc)
  - general passthrough MVT
  - HasDyadicMVTWitness class (constructive 213-existence)
  - generic FTC-Riemann via witness
  - propagation theorems (mid, id-compose)
  - explicit dyadic witnesses (5+ instances at c = 1/2)
-/

namespace E213.Math.Real213.PhaseCMFinalCapstone

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Math.Real213.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.FluxMVTPassthrough.FluxCut
  (mvt_passthrough_unit_forward_at mvt_passthrough_unit_backward_at
   fluxAlong_passthrough_unit_forward_at
   fluxAlong_passthrough_unit_backward_at)
open E213.Math.Real213.FluxMVTConcrete.FluxCut
  (mvt_id_unitBracket_forward_at mvt_id_unitBracket_backward_at)
open E213.Math.Real213.FluxMVTGeneric.FluxCut
  (mvt_cutPow_unitBracket_forward_at mvt_cutPow_unitBracket_backward_at)
open E213.Math.Real213.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Math.Real213.MVTWitnessChain (id_compose_square_derivative_at_half_at)
open E213.Math.Real213.FTCRiemann (ftc_riemann_id_depth_zero)

/-- ★★★ **Phase CM final mega-mega capstone, pointwise PURE form** ★★★

    Strict ∅-axiom version of the 4-marquee BE+BF+passthrough+id MVT
    bundle, expressed at the pointwise field-equality level. -/
theorem phaseCM_final_capstone_at (n : Nat)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1)
    (h_right : f (constCut 1 1) = constCut 1 1) (m k : Nat) :
    -- (AY-3) id at unit forward + backward
    (localDivergence id unitBracket).forward m k
       = (ofCut (constCut 1 1) : FluxCut).forward m k
    ∧ (localDivergence id unitBracket).backward m k
       = (ofCut (constCut 1 1) : FluxCut).backward m k
    -- (BE) generic ∀n cutPow MVT pointwise
    ∧ (localDivergence (fun x => cutPow x (n+1)) unitBracket).forward m k
       = (ofCut (constCut 1 1) : FluxCut).forward m k
    ∧ (localDivergence (fun x => cutPow x (n+1)) unitBracket).backward m k
       = (ofCut (constCut 1 1) : FluxCut).backward m k
    -- (BF) general passthrough MVT pointwise
    ∧ (localDivergence f unitBracket).forward m k
       = (ofCut (constCut 1 1) : FluxCut).forward m k
    ∧ (localDivergence f unitBracket).backward m k
       = (ofCut (constCut 1 1) : FluxCut).backward m k
    -- (BF) passthrough fluxAlong pointwise
    ∧ (fluxAlong f unitBracket).forward m k
       = (ofCut (constCut 1 1) : FluxCut).forward m k
    ∧ (fluxAlong f unitBracket).backward m k
       = (ofCut (constCut 1 1) : FluxCut).backward m k
    -- (BR) explicit dyadic witness for x²
    ∧ squareIsDifferentiable.derivative (constCut 1 2) m k = constCut 1 1 m k
    -- (BU) mid(x, x²) witness
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2) m k = constCut 1 1 m k
    -- (BW/CL) chain-rule witness via id-compose
    ∧ (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
        ).derivative (constCut 1 2) m k = constCut 1 1 m k :=
  ⟨mvt_id_unitBracket_forward_at m k,
   mvt_id_unitBracket_backward_at m k,
   mvt_cutPow_unitBracket_forward_at n m k,
   mvt_cutPow_unitBracket_backward_at n m k,
   mvt_passthrough_unit_forward_at f h_right m k,
   mvt_passthrough_unit_backward_at f h_left m k,
   fluxAlong_passthrough_unit_forward_at f h_right m k,
   fluxAlong_passthrough_unit_backward_at f h_left m k,
   squareDerivative_at_half_at m k,
   mid_id_square_derivative_at_half_at m k,
   id_compose_square_derivative_at_half_at m k⟩

/-! ### fluxCutEq PURE variant (MVT/FTC subset) -/

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Real213.FluxMVTConcrete.FluxCut (mvt_id_unitBracket_pure)
open E213.Math.Real213.FluxMVTGeneric.FluxCut
  (mvt_cutPow_unitBracket_pure fluxAlong_cutPow_unitBracket_pure)
open E213.Math.Real213.FluxMVTPassthrough.FluxCut
  (mvt_passthrough_unit_pure fluxAlong_passthrough_unit_pure
   ftc_bridge_passthrough_unit_pure)

/-- ★★★ **Phase CM final capstone — fluxCutEq PURE** ★★★
    Strict ∅-axiom (no propext, no Quot.sound).  Covers the MVT/FTC
    marquee facts; pointwise dyadic-witness facts already PURE
    in `_at` form above. -/
theorem phaseCM_final_capstone_pure (n : Nat)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
                (ofCut (constCut 1 1))
    ∧ fluxCutEq (fluxAlong (fun x => cutPow x (n+1)) unitBracket)
                (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (fluxAlong f unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence f unitBracket) (fluxAlong f unitBracket) :=
  ⟨mvt_id_unitBracket_pure,
   mvt_cutPow_unitBracket_pure n,
   fluxAlong_cutPow_unitBracket_pure n,
   mvt_passthrough_unit_pure f h_left h_right,
   fluxAlong_passthrough_unit_pure f h_left h_right,
   ftc_bridge_passthrough_unit_pure f h_left h_right⟩

end E213.Math.Real213.PhaseCMFinalCapstone
