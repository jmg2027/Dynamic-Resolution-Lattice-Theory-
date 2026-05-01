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

/-- ★ **HasDyadicMVTWitness** for an IsDifferentiable f: a *dyadic*
    cut c such that f'(c) = constCut 1 1. -/
structure HasDyadicMVTWitness {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : IsDifferentiable f) where
  witness : Nat → Nat → Bool
  proof : sf.derivative witness = constCut 1 1

namespace HasDyadicMVTWitness

/-- ★ x² has dyadic MVT witness c = 1/2. -/
def square : HasDyadicMVTWitness squareIsDifferentiable :=
  { witness := constCut 1 2
    proof := squareDerivative_at_half }

/-- Generic MVT existence from the class. -/
theorem mvt_exists {f sf} (w : @HasDyadicMVTWitness f sf) :
    ∃ c, sf.derivative c = constCut 1 1 :=
  ⟨w.witness, w.proof⟩

end HasDyadicMVTWitness

/-- Phase BT capstone: x² has constructive MVT existence. -/
theorem square_has_dyadic_witness :
    ∃ c, squareIsDifferentiable.derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.square

/-- The witness for x² is exactly 1/2 (≥ 0 and ≤ 1). -/
theorem square_witness_is_half :
    HasDyadicMVTWitness.square.witness = constCut 1 2 := rfl

/-- Phase BT bundle: explicit witness + existential. -/
theorem mvt_witness_capstone :
    -- (1) x² has explicit dyadic witness c = 1/2
    HasDyadicMVTWitness.square.witness = constCut 1 2
    -- (2) Witness validates: f'(1/2) = 1
    ∧ squareIsDifferentiable.derivative HasDyadicMVTWitness.square.witness
       = constCut 1 1
    -- (3) Hence MVT existence (constructive)
    ∧ ∃ c, squareIsDifferentiable.derivative c = constCut 1 1:=
  ⟨rfl, HasDyadicMVTWitness.square.proof, square_has_dyadic_witness⟩

end E213.Math.Real213.HasDyadicMVTWitness
