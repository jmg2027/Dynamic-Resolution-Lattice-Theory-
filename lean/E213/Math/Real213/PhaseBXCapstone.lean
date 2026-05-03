import E213.Math.Real213.MVTWitnessChain

/-!
# Research.Real213PhaseBXCapstone

Phase BX: capstone for the constructive MVT witness arc (BT-BW).

Bundles all known constructive dyadic MVT witnesses + the
HasDyadicMVTWitness class infrastructure.
-/

namespace E213.Math.Real213.PhaseBXCapstone

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable composeIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Math.Real213.MVTWitnessChain
  (id_compose_square_derivative_at_half_at)

/-- ★ **Phase BX pointwise PURE capstone** ★

    Strict ∅-axiom version covering the full (BT/BU/BV/BW) MVT witness
    arc at the pointwise field-equality level. -/
theorem phaseBX_witness_capstone_at (c : Nat → Nat → Bool) (m k : Nat) :
    -- (BT) ★ explicit dyadic MVT witness for x² at c = 1/2
    squareIsDifferentiable.derivative (constCut 1 2) m k = constCut 1 1 m k
    -- (BU) HasDyadicMVTWitness for mid(x, x²)
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2) m k = constCut 1 1 m k
    -- (BV) id at c = 0
    ∧ idIsDifferentiable.derivative (constCut 0 1) m k = constCut 1 1 m k
    -- (BV) id at c = 1
    ∧ idIsDifferentiable.derivative (constCut 1 1) m k = constCut 1 1 m k
    -- (BV) id at any c
    ∧ idIsDifferentiable.derivative c m k = constCut 1 1 m k
    -- (BW) id ∘ x² witness c = 1/2
    ∧ (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
        ).derivative (constCut 1 2) m k = constCut 1 1 m k :=
  ⟨squareDerivative_at_half_at m k,
   mid_id_square_derivative_at_half_at m k,
   rfl, rfl, rfl,
   id_compose_square_derivative_at_half_at m k⟩

end E213.Math.Real213.PhaseBXCapstone
