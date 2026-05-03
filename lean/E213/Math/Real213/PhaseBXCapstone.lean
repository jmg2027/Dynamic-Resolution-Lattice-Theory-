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
open E213.Math.Real213.HasDyadicMVTWitness
  (HasDyadicMVTWitness square_has_dyadic_witness)
open E213.Math.Real213.HasDyadicMVTWitness.HasDyadicMVTWitness (square)
open E213.Math.Real213.FluxMVTMore.HasDyadicMVTWitness (mid_id_square)
open E213.Math.Real213.MVTWitnessChain.HasDyadicMVTWitness (id_compose_square)

/-- ★ **Phase BX constructive MVT witness capstone**: 7-fact bundle. -/
theorem phaseBX_witness_capstone (c : Nat → Nat → Bool) :
    -- (BT) HasDyadicMVTWitness for x²
    squareIsDifferentiable.derivative
        square.witness = constCut 1 1
    -- (BU) HasDyadicMVTWitness for mid(x, x²)
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative mid_id_square.witness = constCut 1 1
    -- (BV) id at c = 0
    ∧ idIsDifferentiable.derivative (constCut 0 1) = constCut 1 1
    -- (BV) id at c = 1
    ∧ idIsDifferentiable.derivative (constCut 1 1) = constCut 1 1
    -- (BV) id at any c
    ∧ idIsDifferentiable.derivative c = constCut 1 1
    -- (BW) id ∘ x² witness c = 1/2
    ∧ (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
        ).derivative id_compose_square.witness
       = constCut 1 1
    -- (BT-BW) Existential MVT for all of these
    ∧ (∃ c, squareIsDifferentiable.derivative c = constCut 1 1) :=
  ⟨square.proof,
   mid_id_square.proof,
   rfl, rfl, rfl,
   id_compose_square.proof,
   square_has_dyadic_witness⟩

/-- ★ **Phase BX pointwise PURE capstone** ★

    Strict ∅-axiom restriction of `phaseBX_witness_capstone` to the
    rfl-reducible (BV) facts: id's derivative is constant 1 at every
    cut.  The (BT/BU/BW) facts use `squareDerivative_at_half` etc.
    which are gated by the `cutMul_*_one*_at` chain — those continue
    to live in the function-eq capstone above. -/
theorem phaseBX_witness_capstone_at (c : Nat → Nat → Bool) (m k : Nat) :
    -- (BV) id at c = 0
    idIsDifferentiable.derivative (constCut 0 1) m k = constCut 1 1 m k
    -- (BV) id at c = 1
    ∧ idIsDifferentiable.derivative (constCut 1 1) m k = constCut 1 1 m k
    -- (BV) id at any c
    ∧ idIsDifferentiable.derivative c m k = constCut 1 1 m k :=
  ⟨rfl, rfl, rfl⟩

end E213.Math.Real213.PhaseBXCapstone
