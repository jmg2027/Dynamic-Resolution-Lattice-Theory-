import E213.Math.Real213.MVTWitnessCatalog
import E213.Math.Real213.DifferentiableCompose

/-!
# Research.Real213MVTWitnessChain

Phase BW: chain-rule MVT witnesses (compose).

For composition g ∘ f with both passthrough, the chain-rule
derivative is g'(f(c)) · f'(c).  When c is f's witness AND g'
is constant 1 (i.e., g = id), the chain-rule witness is f's witness.

  id ∘ x² witness: c = 1/2
-/

namespace E213.Math.Real213.MVTWitnessChain

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)

/-- ★ id ∘ x² derivative at c = 1/2 = 1 (propEq).
    Same function as x² but constructed via chain rule. -/
theorem id_compose_square_derivative_at_half :
    (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable).derivative
        (constCut 1 2) = constCut 1 1 := by
  show cutMul (idIsDifferentiable.derivative ((fun x => cutMul x x)
              (constCut 1 2)))
              (squareIsDifferentiable.derivative (constCut 1 2))
       = constCut 1 1
  show cutMul (constCut 1 1) (squareIsDifferentiable.derivative (constCut 1 2))
       = constCut 1 1
  rw [squareDerivative_at_half, cutMul_one_one]

/-- HasDyadicMVTWitness instance for id ∘ x². -/
def HasDyadicMVTWitness.id_compose_square :
    HasDyadicMVTWitness
      (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable) :=
  { witness := constCut 1 2
    proof := id_compose_square_derivative_at_half }

/-- id ∘ x² has constructive MVT existence. -/
theorem id_compose_square_has_dyadic_witness :
    ∃ c, (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
            ).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.id_compose_square

/-- Phase BW capstone: chain-rule MVT witness for id ∘ x². -/
theorem chain_rule_witness_capstone :
    -- (1) id ∘ x² witness at c = 1/2
    (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable).derivative
        (constCut 1 2) = constCut 1 1
    -- (2) Existential MVT
    ∧ (∃ c, (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
              ).derivative c = constCut 1 1) :=
  ⟨id_compose_square_derivative_at_half,
   id_compose_square_has_dyadic_witness⟩

end E213.Math.Real213.MVTWitnessChain
