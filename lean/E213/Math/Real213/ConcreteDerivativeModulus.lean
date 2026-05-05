import E213.Math.Real213.DifferentiableInstances

/-!
# Concrete polynomial derivative modulus — sharp `(n-1)·k` pattern

The concrete `IsDifferentiable` instances `squareIsDiff`, `cubeIsDiff`,
… `hexadecicIsDiff` all yield derivative modulus `(n-1)·k`, matching
the mathematical fact that `d/dx [x^n]` has degree `n-1`.

The generic `cutPowFnIsDifferentiable n` chain gives `n·k` due to
structural overhead, so the concrete instances are **strictly sharper**.

| polynomial | function modulus | derivative modulus |
|------------|-----------------:|-------------------:|
| x²         | 2k               | k                  |
| x³         | 3k               | 2k                 |
| x⁴         | 4k               | 3k                 |
| x⁵         | 5k               | 4k                 |
| x⁶         | 6k               | 5k                 |
| x⁷         | 7k               | 6k                 |
| x⁸         | 8k               | 7k                 |
| x⁹         | 9k               | 8k                 |
| x¹⁰        | 10k              | 9k                 |
| x¹²        | 12k              | 11k                |
| x¹⁶        | 16k              | 15k                |

(Consolidated 2026-05-05 from 4 phase files: ConcreteDerivativeModulus
[degrees 2-4] + ConcreteDerivativeModulusHigh [5-8] +
ConcreteDerivativeModulusFinal [9, 10, 12, 16] + ConcreteDerivativeMega.
Per-stage capstone bundles dropped — only the 11 unique modulus
theorems remain.)
-/

namespace E213.Math.Real213.ConcreteDerivativeModulus

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
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
open E213.Math.Real213.DifferentiableHighOrder
  (nonicIsDifferentiable decicIsDifferentiable dodecicIsDifferentiable
   hexadecicIsDifferentiable
   nonicIsDifferentiable_modulus decicIsDifferentiable_modulus
   dodecicIsDifferentiable_modulus hexadecicIsDifferentiable_modulus)

/-- Helper: a*k + b*k = (a+b)*k via Nat213.add_mul. -/
private theorem coef_add (a b k : Nat) :
    a * k + b * k = (a + b) * k :=
  (E213.Tactic.Nat213.add_mul a b k).symm

/-- d/dx [x²] modulus = k  (linear, degree 1). -/
theorem squareIsDifferentiable_derivative_modulus (k : Nat) :
    squareIsDifferentiable.derivativeSmooth.linearityModulus k = k := by
  show max (0 + k) (k + 0) = k
  rw [Nat.zero_add, Nat.add_zero]
  exact Nat.max_self k

/-- d/dx [x³] modulus = 2k  (quadratic, degree 2). -/
theorem cubeIsDifferentiable_derivative_modulus (k : Nat) :
    cubeIsDifferentiable.derivativeSmooth.linearityModulus k = 2 * k := by
  show max (0 + squareIsDifferentiable.linearityModulus k)
           (k + squareIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 2 * k
  rw [squareIsDifferentiable_modulus,
      squareIsDifferentiable_derivative_modulus]
  rw [Nat.zero_add, ← Nat.two_mul]
  exact Nat.max_self (2 * k)

/-- d/dx [x⁴] modulus = 3k  (cubic, degree 3). -/
theorem quarticIsDifferentiable_derivative_modulus (k : Nat) :
    quarticIsDifferentiable.derivativeSmooth.linearityModulus k = 3 * k := by
  show max (squareIsDifferentiable.derivativeSmooth.linearityModulus k
            + squareIsDifferentiable.linearityModulus k)
           (squareIsDifferentiable.linearityModulus k
            + squareIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 3 * k
  rw [squareIsDifferentiable_derivative_modulus,
      squareIsDifferentiable_modulus]
  have e1 : k + 2 * k = 3 * k := by
    rw [show (3:Nat) = 1 + 2 from rfl, E213.Tactic.Nat213.add_mul, Nat.one_mul]
  have e2 : 2 * k + k = 3 * k := by
    rw [show (3:Nat) = 2 + 1 from rfl, E213.Tactic.Nat213.add_mul, Nat.one_mul]
  rw [e1, e2]
  exact Nat.max_self (3 * k)

end E213.Math.Real213.ConcreteDerivativeModulus

namespace E213.Math.Real213.ConcreteDerivativeModulus

/-- d/dx [x⁵] modulus = 4k. -/
theorem quinticIsDifferentiable_derivative_modulus (k : Nat) :
    quinticIsDifferentiable.derivativeSmooth.linearityModulus k = 4 * k := by
  show max (squareIsDifferentiable.derivativeSmooth.linearityModulus k
            + cubeIsDifferentiable.linearityModulus k)
           (squareIsDifferentiable.linearityModulus k
            + cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 4 * k
  rw [squareIsDifferentiable_derivative_modulus, cubeIsDifferentiable_modulus,
      squareIsDifferentiable_modulus, cubeIsDifferentiable_derivative_modulus]
  have hL : k + 3 * k = 4 * k := by
    have e := coef_add 1 3 k
    rw [Nat.one_mul] at e
    exact e
  have hR : 2 * k + 2 * k = 4 * k := coef_add 2 2 k
  rw [hL, hR]
  exact Nat.max_self (4 * k)

/-- d/dx [x⁶] modulus = 5k. -/
theorem sexticIsDifferentiable_derivative_modulus (k : Nat) :
    sexticIsDifferentiable.derivativeSmooth.linearityModulus k = 5 * k := by
  show max (cubeIsDifferentiable.derivativeSmooth.linearityModulus k
            + cubeIsDifferentiable.linearityModulus k)
           (cubeIsDifferentiable.linearityModulus k
            + cubeIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 5 * k
  rw [cubeIsDifferentiable_derivative_modulus, cubeIsDifferentiable_modulus]
  rw [coef_add 2 3 k, coef_add 3 2 k]
  exact Nat.max_self (5 * k)

/-- d/dx [x⁷] modulus = 6k. -/
theorem septicIsDifferentiable_derivative_modulus (k : Nat) :
    septicIsDifferentiable.derivativeSmooth.linearityModulus k = 6 * k := by
  show max (cubeIsDifferentiable.derivativeSmooth.linearityModulus k
            + quarticIsDifferentiable.linearityModulus k)
           (cubeIsDifferentiable.linearityModulus k
            + quarticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 6 * k
  rw [cubeIsDifferentiable_derivative_modulus, quarticIsDifferentiable_modulus,
      cubeIsDifferentiable_modulus, quarticIsDifferentiable_derivative_modulus]
  rw [coef_add 2 4 k, coef_add 3 3 k]
  exact Nat.max_self (6 * k)

/-- d/dx [x⁸] modulus = 7k. -/
theorem octicIsDifferentiable_derivative_modulus (k : Nat) :
    octicIsDifferentiable.derivativeSmooth.linearityModulus k = 7 * k := by
  show max (quarticIsDifferentiable.derivativeSmooth.linearityModulus k
            + quarticIsDifferentiable.linearityModulus k)
           (quarticIsDifferentiable.linearityModulus k
            + quarticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 7 * k
  rw [quarticIsDifferentiable_derivative_modulus, quarticIsDifferentiable_modulus]
  rw [coef_add 3 4 k, coef_add 4 3 k]
  exact Nat.max_self (7 * k)

end E213.Math.Real213.ConcreteDerivativeModulus

namespace E213.Math.Real213.ConcreteDerivativeModulus

/-- d/dx [x⁹] modulus = 8k. -/
theorem nonicIsDifferentiable_derivative_modulus (k : Nat) :
    nonicIsDifferentiable.derivativeSmooth.linearityModulus k = 8 * k := by
  show max (quarticIsDifferentiable.derivativeSmooth.linearityModulus k
            + quinticIsDifferentiable.linearityModulus k)
           (quarticIsDifferentiable.linearityModulus k
            + quinticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 8 * k
  rw [quarticIsDifferentiable_derivative_modulus,
      quinticIsDifferentiable_modulus,
      quarticIsDifferentiable_modulus,
      quinticIsDifferentiable_derivative_modulus]
  rw [coef_add 3 5 k, coef_add 4 4 k]
  exact Nat.max_self (8 * k)

/-- d/dx [x¹⁰] modulus = 9k. -/
theorem decicIsDifferentiable_derivative_modulus (k : Nat) :
    decicIsDifferentiable.derivativeSmooth.linearityModulus k = 9 * k := by
  show max (quinticIsDifferentiable.derivativeSmooth.linearityModulus k
            + quinticIsDifferentiable.linearityModulus k)
           (quinticIsDifferentiable.linearityModulus k
            + quinticIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 9 * k
  rw [quinticIsDifferentiable_derivative_modulus,
      quinticIsDifferentiable_modulus]
  rw [coef_add 4 5 k, coef_add 5 4 k]
  exact Nat.max_self (9 * k)

/-- d/dx [x¹²] modulus = 11k. -/
theorem dodecicIsDifferentiable_derivative_modulus (k : Nat) :
    dodecicIsDifferentiable.derivativeSmooth.linearityModulus k = 11 * k := by
  show max (quarticIsDifferentiable.derivativeSmooth.linearityModulus k
            + octicIsDifferentiable.linearityModulus k)
           (quarticIsDifferentiable.linearityModulus k
            + octicIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 11 * k
  rw [quarticIsDifferentiable_derivative_modulus,
      octicIsDifferentiable_modulus,
      quarticIsDifferentiable_modulus,
      octicIsDifferentiable_derivative_modulus]
  rw [coef_add 3 8 k, coef_add 4 7 k]
  exact Nat.max_self (11 * k)

/-- d/dx [x¹⁶] modulus = 15k. -/
theorem hexadecicIsDifferentiable_derivative_modulus (k : Nat) :
    hexadecicIsDifferentiable.derivativeSmooth.linearityModulus k = 15 * k := by
  show max (octicIsDifferentiable.derivativeSmooth.linearityModulus k
            + octicIsDifferentiable.linearityModulus k)
           (octicIsDifferentiable.linearityModulus k
            + octicIsDifferentiable.derivativeSmooth.linearityModulus k)
       = 15 * k
  rw [octicIsDifferentiable_derivative_modulus, octicIsDifferentiable_modulus]
  rw [coef_add 7 8 k, coef_add 8 7 k]
  exact Nat.max_self (15 * k)

end E213.Math.Real213.ConcreteDerivativeModulus
