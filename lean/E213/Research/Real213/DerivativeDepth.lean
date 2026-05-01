import E213.Research.Real213.DerivativeForms
import E213.Research.Real213.ResolutionDepth

/-!
# Research.Real213DerivativeDepth: derivative resolution depth

Phase AD-3: linearityModulus of the derivative for each constructor.

## Resolution Depth Principle (extended)

For polynomials, the derivative carries the **same** linearity modulus
as the original function: degree × n.  This is the constructive
constructive-analysis analog of "differentiation preserves smoothness
class" — except in 213 it's a sharper statement carrying explicit
modulus equality.

  d/dx [x]      modulus = 0     (derivative is constant 1)
  d/dx [c]      modulus = 0     (derivative is constant 0)
  d/dx [x^n]    modulus = n*k   (matches f modulus)
-/

namespace E213.Research.Real213.DerivativeDepth

open E213.Firmware E213.Hypervisor

/-- Identity's derivative (= constant 1) has resolution depth 0. -/
theorem id_derivative_modulus (k : Nat) :
    idIsDifferentiable.derivativeSmooth.linearityModulus k = 0 := rfl

/-- Constant's derivative (= constant 0) has resolution depth 0. -/
theorem const_derivative_modulus (c : Nat → Nat → Bool) (k : Nat) :
    (constIsDifferentiable c).derivativeSmooth.linearityModulus k = 0 := rfl

/-- Polynomial chain n=0: derivative modulus = 0. -/
theorem cutPow0_derivative_modulus (k : Nat) :
    (cutPowFnIsDifferentiable 0).derivativeSmooth.linearityModulus k = 0 := rfl

/-- Polynomial chain function modulus (via IsDifferentiable's IsSmooth). -/
theorem cutPowFnIsDifferentiable_modulus (n k : Nat) :
    (cutPowFnIsDifferentiable n).linearityModulus k = n * k := by
  induction n with
  | zero => show 0 = 0 * k; rw [Nat.zero_mul]
  | succ m ih =>
    show (cutPowFnIsDifferentiable m).linearityModulus k + k = (m + 1) * k
    rw [ih, Nat.add_mul, Nat.one_mul]

/-- **Polynomial derivative resolution depth**: matches the function.

    For `cutPow x n`, the derivative's linearityModulus equals
    `n * k` — the same scaling as the function itself.  This is
    the 213 dyadic analog of "differentiation is a bounded
    operation on the polynomial class". -/
theorem cutPowFn_derivative_modulus (n k : Nat) :
    (cutPowFnIsDifferentiable n).derivativeSmooth.linearityModulus k = n * k := by
  induction n with
  | zero => show 0 = 0 * k; rw [Nat.zero_mul]
  | succ m ih =>
    show max ((cutPowFnIsDifferentiable m).derivativeSmooth.linearityModulus k + k)
             ((cutPowFnIsDifferentiable m).linearityModulus k + 0)
         = (m + 1) * k
    rw [ih, cutPowFnIsDifferentiable_modulus, Nat.add_zero,
        Nat.add_mul, Nat.one_mul]
    exact Nat.max_eq_left (Nat.le_add_right _ _)

/-- **AD-3 unified capstone**: polynomial chain — function and
    derivative both have linearityModulus = n*k. -/
theorem polynomial_function_and_derivative_modulus (n k : Nat) :
    (cutPowFnIsDifferentiable n).linearityModulus k = n * k
    ∧ (cutPowFnIsDifferentiable n).derivativeSmooth.linearityModulus k = n * k :=
  ⟨cutPowFnIsDifferentiable_modulus n k, cutPowFn_derivative_modulus n k⟩

end E213.Research.Real213.DerivativeDepth
