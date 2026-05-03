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
open E213.Math.Real213.FluxMVTWitness
  (squareDerivative_at_half squareDerivative_at_half_at)
open E213.Math.Real213.FluxMVTMore
  (mid_id_square_derivative_at_half mid_id_square_derivative_at_half_at)
open E213.Math.Real213.CutMulOne (cutMul_one_one cutMul_one_one_at)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)

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

/-- ★ id-compose witness propagation at c = 1/2, pointwise (PURE). -/
theorem id_compose_witness_propagates_at {f} (sf : IsDifferentiable f)
    (hf : ∀ m k, sf.derivative (constCut 1 2) m k = constCut 1 1 m k)
    (m k : Nat) :
    (composeIsDifferentiable sf idIsDifferentiable).derivative
        (constCut 1 2) m k = constCut 1 1 m k := by
  show cutMul (constCut 1 1) (sf.derivative (constCut 1 2)) m k
       = constCut 1 1 m k
  show cutMulOuter (constCut 1 1) (sf.derivative (constCut 1 2))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1) (sf.derivative (constCut 1 2))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (sf.derivative (constCut 1 2)) (constCut 1 1)
      (fun _ _ => rfl) (fun m' _ => hf m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_one_at m k

/-- ★ Phase CL capstone (PURE) — id-compose propagation pointwise. -/
theorem id_compose_propagation_capstone_pure :
    (∀ m k, (composeIsDifferentiable squareIsDifferentiable
              idIsDifferentiable).derivative (constCut 1 2) m k
            = constCut 1 1 m k)
    ∧ (∀ m k, (composeIsDifferentiable
                (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
                idIsDifferentiable).derivative (constCut 1 2) m k
              = constCut 1 1 m k) :=
  ⟨id_compose_witness_propagates_at squareIsDifferentiable
     squareDerivative_at_half_at,
   id_compose_witness_propagates_at
     (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
     mid_id_square_derivative_at_half_at⟩

end E213.Math.Real213.FluxMVTPropagateCompose
