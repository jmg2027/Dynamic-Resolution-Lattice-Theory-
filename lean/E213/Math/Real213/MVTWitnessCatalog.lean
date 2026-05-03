import E213.Math.Real213.FluxMVTMore

/-!
# Research.Real213MVTWitnessCatalog

Phase BV: catalog of HasDyadicMVTWitness instances.

The class is non-trivially populated: any *dyadic witness* point
yields constructive MVT existence.  For id (linear) every point
is a witness.  For x², c = 1/2.  For mid(x, x²), c = 1/2.

  HasDyadicMVTWitness.id_at_zero    : c = 0 (any point works for id)
  HasDyadicMVTWitness.id_at_half    : c = 1/2
  HasDyadicMVTWitness.id_at_one     : c = 1
-/

namespace E213.Math.Real213.MVTWitnessCatalog

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.HasDyadicMVTWitness
  (HasDyadicMVTWitness HasDyadicMVTWitness_at)
open E213.Math.Real213.FluxMVTWitness
  (squareDerivative_at_half squareDerivative_at_half_at)
open E213.Math.Real213.FluxMVTMore
  (mid_id_square_derivative_at_half mid_id_square_derivative_at_half_at)

namespace HasDyadicMVTWitness

/-- id derivative at any point = 1 (constant 1).  Witness c = 0. -/
def id_at_zero : HasDyadicMVTWitness idIsDifferentiable :=
  { witness := constCut 0 1, proof := rfl }

/-- id witness c = 1/2. -/
def id_at_half : HasDyadicMVTWitness idIsDifferentiable :=
  { witness := constCut 1 2, proof := rfl }

/-- id witness c = 1. -/
def id_at_one : HasDyadicMVTWitness idIsDifferentiable :=
  { witness := constCut 1 1, proof := rfl }

/-- id witness at any concrete cut. -/
def id_at_any (c : Nat → Nat → Bool) :
    HasDyadicMVTWitness idIsDifferentiable :=
  { witness := c, proof := rfl }

end HasDyadicMVTWitness

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

/-- Phase BV capstone: at least 5 functions have constructive dyadic
    MVT witnesses (id at any of {0, 1/2, 1}, x² at 1/2, mid(x, x²) at 1/2). -/
theorem mvt_witness_catalog_capstone :
    -- (1) id at c = 0
    idIsDifferentiable.derivative (constCut 0 1) = constCut 1 1
    -- (2) id at c = 1/2
    ∧ idIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    -- (3) id at c = 1 (i.e., the right endpoint of [0,1])
    ∧ idIsDifferentiable.derivative (constCut 1 1) = constCut 1 1
    -- (4) x² at c = 1/2
    ∧ squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    -- (5) mid(x, x²) at c = 1/2
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2) = constCut 1 1 :=
  ⟨rfl, rfl, rfl, squareDerivative_at_half,
   mid_id_square_derivative_at_half⟩

/-- ★ Phase BV _at capstone (PURE pointwise). -/
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

end E213.Math.Real213.MVTWitnessCatalog
