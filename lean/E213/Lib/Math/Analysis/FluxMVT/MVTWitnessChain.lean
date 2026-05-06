import E213.Lib.Math.Analysis.FluxMVT.MVTWitnessCatalog
import E213.Lib.Math.Analysis.Differentiation.DifferentiableCompose

import E213.Lib.Math.Real213.Core
import E213.Lib.Math.Real213.CutMul
import E213.Lib.Math.Real213.CutMulDetermined
import E213.Lib.Math.Real213.CutMulOne
import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness
import E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# MVTWitnessChain
chain-rule MVT witnesses (compose).

For composition g ∘ f with both passthrough, the chain-rule
derivative is g'(f(c)) · f'(c).  When c is f's witness AND g'
is constant 1 (i.e., g = id), the chain-rule witness is f's witness.

  id ∘ x² witness: c = 1/2
-/

namespace E213.Lib.Math.Analysis.FluxMVT.MVTWitnessChain

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core (Real213)
open E213.Lib.Math.Real213.CutMul (cutMul)
open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable composeIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness (HasDyadicMVTWitness_at)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness.HasDyadicMVTWitness_at
  (mvt_exists_at)
open E213.Lib.Math.Real213.CutMul (cutMulOuter)
open E213.Lib.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Lib.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness (squareDerivative_at_half_at)

/-- ★ id ∘ x² derivative at c = 1/2 = 1 — pointwise (∅-axiom). -/
theorem id_compose_square_derivative_at_half_at (m k : Nat) :
    (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable).derivative
        (constCut 1 2) m k = constCut 1 1 m k := by
  show cutMul (constCut 1 1)
              (squareIsDifferentiable.derivative (constCut 1 2)) m k
       = constCut 1 1 m k
  -- Push pointwise eq through cutMulOuter: swap inner squareDeriv → constCut 1 1.
  show cutMulOuter (constCut 1 1)
                   (squareIsDifferentiable.derivative (constCut 1 2))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1)
                  (squareIsDifferentiable.derivative (constCut 1 2))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (squareIsDifferentiable.derivative (constCut 1 2)) (constCut 1 1)
      (fun _ _ => rfl)
      (fun m' _ => squareDerivative_at_half_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_one_at m k

/-! ### PURE pointwise variants (∅-axiom) -/

/-- HasDyadicMVTWitness_at instance for id ∘ x² (PURE). -/
def HasDyadicMVTWitness_at.id_compose_square :
    HasDyadicMVTWitness_at
      (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable) :=
  { witness := constCut 1 2
    proof_at := id_compose_square_derivative_at_half_at }

/-- id ∘ x² has pointwise MVT existence (PURE). -/
theorem id_compose_square_has_dyadic_witness_at :
    ∃ c, ∀ m k, (composeIsDifferentiable squareIsDifferentiable
                  idIsDifferentiable).derivative c m k = constCut 1 1 m k :=
  mvt_exists_at HasDyadicMVTWitness_at.id_compose_square

/-- ★ capstone (PURE) — chain-rule MVT witness for id ∘ x². -/
theorem chain_rule_witness_capstone_pure :
    (∀ m k, (composeIsDifferentiable squareIsDifferentiable
              idIsDifferentiable).derivative (constCut 1 2) m k
            = constCut 1 1 m k)
    ∧ (∃ c, ∀ m k, (composeIsDifferentiable squareIsDifferentiable
                     idIsDifferentiable).derivative c m k = constCut 1 1 m k) :=
  ⟨id_compose_square_derivative_at_half_at,
   id_compose_square_has_dyadic_witness_at⟩

end E213.Lib.Math.Analysis.FluxMVT.MVTWitnessChain
