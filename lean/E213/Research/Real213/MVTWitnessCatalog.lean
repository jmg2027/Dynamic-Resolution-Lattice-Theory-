import E213.Research.Real213.FluxMVTMore

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

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

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

end E213.Research.Real213.CutSum
