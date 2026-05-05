import E213.Math.Real213.DifferentiableInstances
import E213.Math.Real213.ClassicCalcMid

/-!
# Research.Real213HasDyadicMVTWitness

Phase BT: ★ class abstracting **constructive dyadic MVT witnesses** ★

For some (lucky) functions, the MVT point c is itself a dyadic cut.
This class bundles the witness with its proof of correctness.

  HasDyadicMVTWitness f := { witness : Cut, proof : f' witness = 1 }

  squareIsDifferentiable: HasDyadicMVTWitness instance with c = 1/2

This separates 213-CONSTRUCTIBLE existence (witness in dyadic
ground type) from CLASSICAL existence (witness in real continuum).
For x², we have the former; for x³, only the latter.
-/

namespace E213.Math.Real213.HasDyadicMVTWitness

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
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
open E213.Math.Real213.FluxMVTWitness (squareDerivative_at_half_at)

/-- ★ **PURE HasDyadicMVTWitness_at**: pointwise proof field
    (∀ m k, ...).  No funext, no Quot.sound.  Sole class — function-eq
    HasDyadicMVTWitness was deleted 2026-05-XX session 27 ('박멸'). -/
structure HasDyadicMVTWitness_at
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : IsDifferentiable f) where
  witness : Nat → Nat → Bool
  proof_at : ∀ m k, sf.derivative witness m k = constCut 1 1 m k

namespace HasDyadicMVTWitness_at

/-- ★ x² has dyadic MVT witness c = 1/2 (PURE _at form). -/
def square_at : HasDyadicMVTWitness_at squareIsDifferentiable :=
  { witness := constCut 1 2
    proof_at := squareDerivative_at_half_at }

/-- Generic MVT existence (pointwise) from the _at class. -/
theorem mvt_exists_at {f sf} (w : @HasDyadicMVTWitness_at f sf) :
    ∃ c, ∀ m k, sf.derivative c m k = constCut 1 1 m k :=
  ⟨w.witness, w.proof_at⟩

end HasDyadicMVTWitness_at

/-- ★ PURE _at variant: x² has dyadic MVT witness pointwise. -/
theorem square_has_dyadic_witness_at :
    ∃ c, ∀ m k, squareIsDifferentiable.derivative c m k = constCut 1 1 m k :=
  HasDyadicMVTWitness_at.mvt_exists_at HasDyadicMVTWitness_at.square_at

/-- The witness for x²_at is exactly 1/2 (PURE — rfl on Nat → Nat → Bool). -/
theorem square_witness_at_is_half :
    HasDyadicMVTWitness_at.square_at.witness = constCut 1 2 := rfl

/-- ★ Phase BT _at bundle (PURE). -/
theorem mvt_witness_capstone_at :
    HasDyadicMVTWitness_at.square_at.witness = constCut 1 2
    ∧ (∀ m k, squareIsDifferentiable.derivative
                HasDyadicMVTWitness_at.square_at.witness m k
              = constCut 1 1 m k)
    ∧ ∃ c, ∀ m k, squareIsDifferentiable.derivative c m k = constCut 1 1 m k :=
  ⟨rfl, HasDyadicMVTWitness_at.square_at.proof_at,
   square_has_dyadic_witness_at⟩

end E213.Math.Real213.HasDyadicMVTWitness
