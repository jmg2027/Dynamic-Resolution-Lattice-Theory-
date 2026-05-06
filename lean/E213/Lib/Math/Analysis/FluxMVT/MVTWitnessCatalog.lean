import E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitnessCombinators
import E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness

import E213.Lib.Math.Real213.Core
import E213.Lib.Math.Real213.CutSumTest
import E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Lib.Math.Analysis.Differentiation.DifferentiableMid
import E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# MVTWitnessCatalog
catalog of HasDyadicMVTWitness instances.

The class is non-trivially populated: any *dyadic witness* point
yields constructive MVT existence.  For id (linear) every point
is a witness.  For x², c = 1/2.  For mid(x, x²), c = 1/2.

  HasDyadicMVTWitness.id_at_zero    : c = 0 (any point works for id)
  HasDyadicMVTWitness.id_at_half    : c = 1/2
  HasDyadicMVTWitness.id_at_one     : c = 1
-/

namespace E213.Lib.Math.Analysis.FluxMVT.MVTWitnessCatalog

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core (Real213)
open E213.Lib.Math.Real213.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableMid (midIsDifferentiable)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness (HasDyadicMVTWitness_at)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Lib.Math.Analysis.FluxMVTMore (mid_id_square_derivative_at_half_at)

namespace HasDyadicMVTWitness_at

/-- id derivative at any point = 1 (PURE _at form). -/
def id_at_zero_at : HasDyadicMVTWitness_at idIsDifferentiable :=
  { witness := constCut 0 1, proof_at := fun _ _ => rfl }

def id_at_half_at : HasDyadicMVTWitness_at idIsDifferentiable :=
  { witness := constCut 1 2, proof_at := fun _ _ => rfl }

def id_at_one_at : HasDyadicMVTWitness_at idIsDifferentiable :=
  { witness := constCut 1 1, proof_at := fun _ _ => rfl }

def id_at_any_at (c : Nat → Nat → Bool) :
    HasDyadicMVTWitness_at idIsDifferentiable :=
  { witness := c, proof_at := fun _ _ => rfl }

end HasDyadicMVTWitness_at

/-- ★ _at capstone (PURE pointwise). -/
theorem mvt_witness_catalog_capstone_at :
    (∀ m k, idIsDifferentiable.derivative (constCut 0 1) m k
              = constCut 1 1 m k)
    ∧ (∀ m k, idIsDifferentiable.derivative (constCut 1 2) m k
              = constCut 1 1 m k)
    ∧ (∀ m k, idIsDifferentiable.derivative (constCut 1 1) m k
              = constCut 1 1 m k)
    ∧ (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
              = constCut 1 1 m k)
    ∧ (∀ m k, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2) m k = constCut 1 1 m k) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   squareDerivative_at_half_at,
   mid_id_square_derivative_at_half_at⟩

end E213.Lib.Math.Analysis.FluxMVT.MVTWitnessCatalog
