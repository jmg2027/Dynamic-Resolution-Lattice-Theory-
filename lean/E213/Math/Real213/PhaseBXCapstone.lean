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

/-- ★ **Phase BX constructive MVT witness capstone**: 7-fact bundle. -/
theorem phaseBX_witness_capstone (c : Nat → Nat → Bool) :
    -- (BT) HasDyadicMVTWitness for x²
    squareIsDifferentiable.derivative
        HasDyadicMVTWitness.square.witness = constCut 1 1
    -- (BU) HasDyadicMVTWitness for mid(x, x²)
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative HasDyadicMVTWitness.mid_id_square.witness = constCut 1 1
    -- (BV) id at c = 0
    ∧ idIsDifferentiable.derivative (constCut 0 1) = constCut 1 1
    -- (BV) id at c = 1
    ∧ idIsDifferentiable.derivative (constCut 1 1) = constCut 1 1
    -- (BV) id at any c
    ∧ idIsDifferentiable.derivative c = constCut 1 1
    -- (BW) id ∘ x² witness c = 1/2
    ∧ (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
        ).derivative HasDyadicMVTWitness.id_compose_square.witness
       = constCut 1 1
    -- (BT-BW) Existential MVT for all of these
    ∧ (∃ c, squareIsDifferentiable.derivative c = constCut 1 1) :=
  ⟨HasDyadicMVTWitness.square.proof,
   HasDyadicMVTWitness.mid_id_square.proof,
   rfl, rfl, rfl,
   HasDyadicMVTWitness.id_compose_square.proof,
   square_has_dyadic_witness⟩

end E213.Math.Real213.PhaseBXCapstone
