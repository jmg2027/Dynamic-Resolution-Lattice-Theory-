import E213.Math.Real213.DifferentiableMegaCoverage
import E213.Math.Real213.DifferentiableCompose
import E213.Math.Real213.DifferentiableAffine
import E213.Math.Real213.PhaseACMinimumProposition

/-!
# Research.Real213PhaseANOmegaCapstone

Phase AN: omega capstone for the differentiation framework — bundles
representative results from Phase AC through AM in one statement.

## Bundled phases

  AC : minimum proposition (forced 0+ ≠ 0-exact)
  AD : id/const derivatives + polynomial derivative modulus
  AE : square/cube/quartic + cutScale/cutHalf
  AF : quintic/sextic/septic/octic
  AG : polynomial 0-8 unified
  AH : 17-phase grand bundle
  AI : affine + polynomial sums
  AJ : composition (chain rule)
  AK : 9-16 high order
  AL : midpoint
  AM : full coverage 0-16
-/

namespace E213.Math.Real213.PhaseANOmegaCapstone

open E213.Firmware E213.Hypervisor

/-- **Phase AN omega capstone**: 13-fact bundle spanning AC-AM. -/
theorem phaseAN_omega_capstone (n a b k : Nat) (x : Nat → Nat → Bool) :
    -- AD: identity derivative is 1
    idIsDifferentiable.derivative x = constCut 1 1
    -- AD: polynomial derivative shares modulus n*k (at given n)
    ∧ (cutPowFnIsDifferentiable n).derivativeSmooth.linearityModulus k = n * k
    -- AE: cutScale derivative = a/b
    ∧ (cutScaleIsDifferentiable a b).derivative = constCutFn (constCut a b)
    -- AE-AM: polynomial moduli (representative samples)
    ∧ squareIsDifferentiable.linearityModulus k = 2 * k
    ∧ quarticIsDifferentiable.linearityModulus k = 4 * k
    ∧ octicIsDifferentiable.linearityModulus k = 8 * k
    ∧ hexadecicIsDifferentiable.linearityModulus k = 16 * k
    -- AI: affine modulus
    ∧ (affineIsDifferentiable a b).linearityModulus k = k
    -- AI: polynomial sum
    ∧ squarePlusIdIsDifferentiable.linearityModulus k = 2 * k
    -- AJ: chain rule modulus = product of degrees
    ∧ squareOfSquareIsDifferentiable.linearityModulus k = 4 * k
    ∧ cubeOfSquareIsDifferentiable.linearityModulus k = 6 * k
    -- AL: midpoint modulus = max of constituents
    ∧ midSquareCubeIsDifferentiable.linearityModulus k = 3 * k
    -- AC: forced 0+ ≠ 0-exact (always true)
    ∧ (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 1
        ≠ (constCut 0 1) 0 1 :=
  ⟨rfl, cutPowFn_derivative_modulus n k, rfl,
   squareIsDifferentiable_modulus k, quarticIsDifferentiable_modulus k,
   octicIsDifferentiable_modulus k, hexadecicIsDifferentiable_modulus k,
   affineIsDifferentiable_modulus a b k,
   squarePlusIdIsDifferentiable_modulus k,
   squareOfSquare_modulus k, cubeOfSquare_modulus k,
   midSquareCube_modulus k,
   (by rw [alwaysTrueUnit_limit_distinct_from_zero.1,
           alwaysTrueUnit_limit_distinct_from_zero.2]
       exact fun h => Bool.noConfusion h)⟩

end E213.Math.Real213.PhaseANOmegaCapstone
