import E213.Math.Real213.DifferentiableHigherPow

/-!
# Research.Real213DifferentiationCapstone

Phase AG: unified polynomial differentiation capstone, degrees 0-8.

Bundles every concrete IsDifferentiable polynomial instance (id,
square, cube, quartic, quintic, sextic, septic, octic) plus their
modulus equalities in one conjunctive theorem.

## Bundled facts

  - idIsDifferentiable                     modulus = k  (= 1·k)
  - squareIsDifferentiable                 modulus = 2k
  - cubeIsDifferentiable                   modulus = 3k
  - quarticIsDifferentiable                modulus = 4k
  - quinticIsDifferentiable                modulus = 5k
  - sexticIsDifferentiable                 modulus = 6k
  - septicIsDifferentiable                 modulus = 7k
  - octicIsDifferentiable                  modulus = 8k
  - cutPowFnIsDifferentiable n             modulus = n·k (generic)
-/

namespace E213.Math.Real213.DifferentiationCapstone

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)

/-- **Polynomial differentiation chain capstone**: degrees 0-8 in
    one conjunction.  Every concrete polynomial IsDifferentiable
    instance + the generic recursive `cutPowFnIsDifferentiable`. -/
theorem polynomial_diff_0_to_8_modulus (n k : Nat) :
    -- Degree 0: identity (linearityModulus k = k)
    idIsDifferentiable.linearityModulus k = k
    -- Degree 2-8: concrete polynomial instances
    ∧ squareIsDifferentiable.linearityModulus k = 2 * k
    ∧ cubeIsDifferentiable.linearityModulus k = 3 * k
    ∧ quarticIsDifferentiable.linearityModulus k = 4 * k
    ∧ quinticIsDifferentiable.linearityModulus k = 5 * k
    ∧ sexticIsDifferentiable.linearityModulus k = 6 * k
    ∧ septicIsDifferentiable.linearityModulus k = 7 * k
    ∧ octicIsDifferentiable.linearityModulus k = 8 * k
    -- Generic: cutPowFnIsDifferentiable n at any n
    ∧ (cutPowFnIsDifferentiable n).linearityModulus k = n * k
    -- Generic: derivative shares modulus n*k
    ∧ (cutPowFnIsDifferentiable n).derivativeSmooth.linearityModulus k = n * k :=
  ⟨rfl,
   squareIsDifferentiable_modulus k, cubeIsDifferentiable_modulus k,
   quarticIsDifferentiable_modulus k, quinticIsDifferentiable_modulus k,
   sexticIsDifferentiable_modulus k, septicIsDifferentiable_modulus k,
   octicIsDifferentiable_modulus k,
   cutPowFnIsDifferentiable_modulus n k,
   cutPowFn_derivative_modulus n k⟩

end E213.Math.Real213.DifferentiationCapstone
