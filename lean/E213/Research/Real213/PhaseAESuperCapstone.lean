import E213.Research.Real213.DifferentiableInstances
import E213.Research.Real213.PhaseACMinimumProposition

/-!
# Research.Real213PhaseAESuperCapstone

Super capstone bundling Phase AC (minimum proposition) + Phase AD
(differentiation framework) + Phase AE (concrete instances) into a
single conjunctive theorem.

## Bundled facts

  AC : analysis line is fully pinned (forced resolution / accumulator)
  AD : d/dx [x] = 1, d/dx [c] = 0, d/dx [x^n] modulus = n*k
  AE : square/cube/quartic concrete IsDifferentiable instances
       cutScale, cutHalf differentiable (linear functions)
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- **Phase AC + AD + AE super capstone**.

    Bundles minimum-proposition (AC) + differentiation framework (AD)
    + concrete polynomial/linear instances (AE) into one statement. -/
theorem phaseAE_super_capstone (n k a b : Nat) (x : Nat → Nat → Bool) :
    -- AC: forced resolution law
    (cutPowFnIsSmooth n).linearityModulus k = n * k
    -- AC: forced 0+ ≠ 0-exact distinctness
    ∧ (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 1
        ≠ (constCut 0 1) 0 1
    -- AD: identity derivative is constant 1
    ∧ idIsDifferentiable.derivative x = constCut 1 1
    -- AD: polynomial derivative shares modulus n*k
    ∧ (cutPowFnIsDifferentiable n).derivativeSmooth.linearityModulus k = n * k
    -- AE: square instance modulus = 2k
    ∧ squareIsDifferentiable.linearityModulus k = 2 * k
    -- AE: cube instance modulus = 3k
    ∧ cubeIsDifferentiable.linearityModulus k = 3 * k
    -- AE: quartic instance modulus = 4k
    ∧ quarticIsDifferentiable.linearityModulus k = 4 * k
    -- AE: linear scaling derivative = a/b
    ∧ (cutScaleIsDifferentiable a b).derivative = constCutFn (constCut a b)
    -- AE: halving derivative = 1/2
    ∧ cutHalfIsDifferentiable.derivative = constCutFn (constCut 1 2) :=
  ⟨cutPowFnIsSmooth_modulus n k,
   (by rw [alwaysTrueUnit_limit_distinct_from_zero.1,
           alwaysTrueUnit_limit_distinct_from_zero.2]
       exact fun h => Bool.noConfusion h),
   rfl,
   cutPowFn_derivative_modulus n k,
   squareIsDifferentiable_modulus k,
   cubeIsDifferentiable_modulus k,
   quarticIsDifferentiable_modulus k,
   rfl, rfl⟩

end E213.Research.Real213.CutSum
