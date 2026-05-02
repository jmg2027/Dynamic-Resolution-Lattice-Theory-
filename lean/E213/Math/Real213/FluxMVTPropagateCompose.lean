import E213.Math.Real213.FluxMVTPropagate

/-!
# Research.Real213FluxMVTPropagateCompose

Phase CL: ★ id-composition witness propagation ★

For g ∘ f via composeIsDifferentiable f g, the chain rule gives
derivative = g'(f(x)) · f'(x).  When g = id, g'(anything) = 1,
so derivative = f'(x).  Hence id ∘ f's witness = f's witness.

  id_compose_witness_propagates : sf witness 1/2 → id ∘ f witness 1/2
-/

namespace E213.Math.Real213.FluxMVTPropagateCompose

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable (IsDifferentiable)

/-- ★ id-compose witness propagation at c = 1/2. -/
theorem id_compose_witness_propagates {f} (sf : IsDifferentiable f)
    (hf : sf.derivative (constCut 1 2) = constCut 1 1) :
    (composeIsDifferentiable sf idIsDifferentiable).derivative
        (constCut 1 2) = constCut 1 1 := by
  show cutMul (idIsDifferentiable.derivative (f (constCut 1 2)))
              (sf.derivative (constCut 1 2)) = constCut 1 1
  show cutMul (constCut 1 1) (sf.derivative (constCut 1 2)) = constCut 1 1
  rw [hf]
  exact cutMul_one_one

/-- ★ Phase CL capstone: id-compose propagation derives BW. -/
theorem id_compose_propagation_capstone :
    -- (1) Generic id-compose propagation
    (∀ {f} (sf : IsDifferentiable f),
      sf.derivative (constCut 1 2) = constCut 1 1 →
      (composeIsDifferentiable sf idIsDifferentiable).derivative
        (constCut 1 2) = constCut 1 1)
    -- (2) Specific: id ∘ x² (BW) — derived via propagation
    ∧ (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
        ).derivative (constCut 1 2) = constCut 1 1
    -- (3) Specific: id ∘ mid(x, x²) — derived via propagation
    ∧ (composeIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        idIsDifferentiable).derivative (constCut 1 2) = constCut 1 1 :=
  ⟨@id_compose_witness_propagates,
   id_compose_witness_propagates squareIsDifferentiable
     squareDerivative_at_half,
   id_compose_witness_propagates
     (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
     mid_id_square_derivative_at_half⟩

end E213.Math.Real213.FluxMVTPropagateCompose
