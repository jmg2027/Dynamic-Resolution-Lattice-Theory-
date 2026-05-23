
import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Mul.CutPow
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.Differentiation.Differentiable
import E213.Lib.Math.Analysis.Differentiation.Smooth
/-!
# Polynomial-chain `IsDifferentiable` instances — degrees 1-16

Concrete `IsDifferentiable` instances paralleling the `IsSmooth` chain
(`squareIsSmooth`, `cubeIsSmooth`, …).  Each derivative shares the
function's `linearityModulus = degree × k`.

Sub-namespaces preserved (cross-layer `open` declarations):

  * `E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances`  — degrees 1-4 + scale/half
  * `E213.Lib.Math.Analysis.DifferentiableHigherPow`  — degrees 5-8
  * `E213.Lib.Math.Analysis.DifferentiableHighOrder`  — degrees 9, 10, 12, 16

( from 3 DifferentiableInstances
[-1, deg 1-4] + DifferentiableHigherPow [, deg 5-8] +
DifferentiableHighOrder [, deg 9-16].  Per-stage capstone
bundles dropped.  Sub-namespaces kept so existing `open … HigherPow`
/ `open … HighOrder` declarations across the codebase stay valid.)

| degree | instance                  | modulus |
|-------:|---------------------------|--------:|
|      1 | (id from `IsDifferentiable`) | k    |
|      2 | `squareIsDifferentiable`  | 2k      |
|      3 | `cubeIsDifferentiable`    | 3k      |
|      4 | `quarticIsDifferentiable` | 4k      |
|      5 | `quinticIsDifferentiable` | 5k      |
|      6 | `sexticIsDifferentiable`  | 6k      |
|      7 | `septicIsDifferentiable`  | 7k      |
|      8 | `octicIsDifferentiable`   | 8k      |
|      9 | `nonicIsDifferentiable`   | 9k      |
|     10 | `decicIsDifferentiable`   | 10k     |
|     12 | `dodecicIsDifferentiable` | 12k     |
|     16 | `hexadecicIsDifferentiable` | 16k   |
-/

namespace E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Bisection.CutBisection (cutHalf)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Mul.CutPow (cutScale)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.Smooth (constIsSmooth cutHalfIsSmooth cutScaleIsSmooth)

/-- x² differentiable. -/
def squareIsDifferentiable : IsDifferentiable (fun x => cutMul x x) :=
  mulIsDifferentiable idIsDifferentiable idIsDifferentiable

/-- x³ differentiable. -/
def cubeIsDifferentiable :
    IsDifferentiable (fun x => cutMul x (cutMul x x)) :=
  mulIsDifferentiable idIsDifferentiable squareIsDifferentiable

/-- x⁴ differentiable. -/
def quarticIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  mulIsDifferentiable squareIsDifferentiable squareIsDifferentiable

/-- d/dx [x²] closed form: 1·x + x·1. -/
theorem square_derivative_form (x : Nat → Nat → Bool) :
    squareIsDifferentiable.derivative x
      = cutSum (cutMul (constCut 1 1) x) (cutMul x (constCut 1 1)) := rfl

theorem squareIsDifferentiable_modulus (k : Nat) :
    squareIsDifferentiable.linearityModulus k = 2 * k := by
  show k + k = 2 * k
  rw [Nat.two_mul]

theorem cubeIsDifferentiable_modulus (k : Nat) :
    cubeIsDifferentiable.linearityModulus k = 3 * k := by
  show k + (k + k) = 3 * k
  have e3 : (3 : Nat) * k = k + k + k := by
    rw [show (3 : Nat) = 1 + 1 + 1 from rfl,
        E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.add_mul, Nat.one_mul]
  rw [e3, Nat.add_assoc]

theorem quarticIsDifferentiable_modulus (k : Nat) :
    quarticIsDifferentiable.linearityModulus k = 4 * k := by
  show (k + k) + (k + k) = 4 * k
  have e4 : (4 : Nat) * k = k + k + k + k := by
    rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl,
        E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.add_mul,
        E213.Tactic.NatHelper.add_mul, Nat.one_mul]
  rw [e4]
  exact (Nat.add_assoc (k+k) k k).symm

/-- (a/b)·x linear scaling. -/
def cutScaleIsDifferentiable (a b : Nat) : IsDifferentiable (cutScale a b) where
  toIsSmooth := cutScaleIsSmooth a b
  derivative := constCutFn (constCut a b)
  derivativeSmooth := constIsSmooth (constCut a b)

def cutHalfIsDifferentiable : IsDifferentiable cutHalf where
  toIsSmooth := cutHalfIsSmooth
  derivative := constCutFn (constCut 1 2)
  derivativeSmooth := constIsSmooth (constCut 1 2)

theorem cutScale_derivative_form (a b : Nat) :
    (cutScaleIsDifferentiable a b).derivative = constCutFn (constCut a b) := rfl

theorem cutHalf_derivative_form :
    cutHalfIsDifferentiable.derivative = constCutFn (constCut 1 2) := rfl

end E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances

namespace E213.Lib.Math.Analysis.DifferentiableHigherPow

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable mulIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus)

/-- x⁵ = x²·x³. -/
def quinticIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) :=
  mulIsDifferentiable squareIsDifferentiable cubeIsDifferentiable

/-- x⁶ = x³·x³. -/
def sexticIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x (cutMul x x))
                                      (cutMul x (cutMul x x))) :=
  mulIsDifferentiable cubeIsDifferentiable cubeIsDifferentiable

/-- x⁷ = x³·x⁴. -/
def septicIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul x (cutMul x x))
                                      (cutMul (cutMul x x) (cutMul x x))) :=
  mulIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable

/-- x⁸ = x⁴·x⁴. -/
def octicIsDifferentiable :
    IsDifferentiable (fun x => cutMul (cutMul (cutMul x x) (cutMul x x))
                                      (cutMul (cutMul x x) (cutMul x x))) :=
  mulIsDifferentiable quarticIsDifferentiable quarticIsDifferentiable

theorem quinticIsDifferentiable_modulus (k : Nat) :
    quinticIsDifferentiable.linearityModulus k = 5 * k := by
  show squareIsDifferentiable.linearityModulus k
       + cubeIsDifferentiable.linearityModulus k = 5 * k
  rw [squareIsDifferentiable_modulus, cubeIsDifferentiable_modulus]
  exact (E213.Tactic.NatHelper.add_mul 2 3 k).symm

theorem sexticIsDifferentiable_modulus (k : Nat) :
    sexticIsDifferentiable.linearityModulus k = 6 * k := by
  show cubeIsDifferentiable.linearityModulus k
       + cubeIsDifferentiable.linearityModulus k = 6 * k
  rw [cubeIsDifferentiable_modulus]
  exact (E213.Tactic.NatHelper.add_mul 3 3 k).symm

theorem septicIsDifferentiable_modulus (k : Nat) :
    septicIsDifferentiable.linearityModulus k = 7 * k := by
  show cubeIsDifferentiable.linearityModulus k
       + quarticIsDifferentiable.linearityModulus k = 7 * k
  rw [cubeIsDifferentiable_modulus, quarticIsDifferentiable_modulus]
  exact (E213.Tactic.NatHelper.add_mul 3 4 k).symm

theorem octicIsDifferentiable_modulus (k : Nat) :
    octicIsDifferentiable.linearityModulus k = 8 * k := by
  show quarticIsDifferentiable.linearityModulus k
       + quarticIsDifferentiable.linearityModulus k = 8 * k
  rw [quarticIsDifferentiable_modulus]
  exact (E213.Tactic.NatHelper.add_mul 4 4 k).symm

end E213.Lib.Math.Analysis.DifferentiableHigherPow

namespace E213.Lib.Math.Analysis.DifferentiableHighOrder

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable mulIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus)
open E213.Lib.Math.Analysis.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)

/-- x⁹ = x⁴·x⁵. -/
def nonicIsDifferentiable :
    IsDifferentiable (fun x =>
      cutMul (cutMul (cutMul x x) (cutMul x x))
             (cutMul (cutMul x x) (cutMul x (cutMul x x)))) :=
  mulIsDifferentiable quarticIsDifferentiable quinticIsDifferentiable

/-- x¹⁰ = x⁵·x⁵. -/
def decicIsDifferentiable :
    IsDifferentiable (fun x =>
      cutMul (cutMul (cutMul x x) (cutMul x (cutMul x x)))
             (cutMul (cutMul x x) (cutMul x (cutMul x x)))) :=
  mulIsDifferentiable quinticIsDifferentiable quinticIsDifferentiable

/-- x¹² = x⁴·x⁸. -/
def dodecicIsDifferentiable :
    IsDifferentiable (fun x =>
      cutMul (cutMul (cutMul x x) (cutMul x x))
             (cutMul (cutMul (cutMul x x) (cutMul x x))
                     (cutMul (cutMul x x) (cutMul x x)))) :=
  mulIsDifferentiable quarticIsDifferentiable octicIsDifferentiable

/-- x¹⁶ = x⁸·x⁸. -/
def hexadecicIsDifferentiable :
    IsDifferentiable (fun x =>
      cutMul (cutMul (cutMul (cutMul x x) (cutMul x x))
                     (cutMul (cutMul x x) (cutMul x x)))
             (cutMul (cutMul (cutMul x x) (cutMul x x))
                     (cutMul (cutMul x x) (cutMul x x)))) :=
  mulIsDifferentiable octicIsDifferentiable octicIsDifferentiable

theorem nonicIsDifferentiable_modulus (k : Nat) :
    nonicIsDifferentiable.linearityModulus k = 9 * k := by
  show quarticIsDifferentiable.linearityModulus k
       + quinticIsDifferentiable.linearityModulus k = 9 * k
  rw [quarticIsDifferentiable_modulus, quinticIsDifferentiable_modulus]
  exact (E213.Tactic.NatHelper.add_mul 4 5 k).symm

theorem decicIsDifferentiable_modulus (k : Nat) :
    decicIsDifferentiable.linearityModulus k = 10 * k := by
  show quinticIsDifferentiable.linearityModulus k
       + quinticIsDifferentiable.linearityModulus k = 10 * k
  rw [quinticIsDifferentiable_modulus]
  exact (E213.Tactic.NatHelper.add_mul 5 5 k).symm

theorem dodecicIsDifferentiable_modulus (k : Nat) :
    dodecicIsDifferentiable.linearityModulus k = 12 * k := by
  show quarticIsDifferentiable.linearityModulus k
       + octicIsDifferentiable.linearityModulus k = 12 * k
  rw [quarticIsDifferentiable_modulus, octicIsDifferentiable_modulus]
  exact (E213.Tactic.NatHelper.add_mul 4 8 k).symm

theorem hexadecicIsDifferentiable_modulus (k : Nat) :
    hexadecicIsDifferentiable.linearityModulus k = 16 * k := by
  show octicIsDifferentiable.linearityModulus k
       + octicIsDifferentiable.linearityModulus k = 16 * k
  rw [octicIsDifferentiable_modulus]
  exact (E213.Tactic.NatHelper.add_mul 8 8 k).symm

end E213.Lib.Math.Analysis.DifferentiableHighOrder
