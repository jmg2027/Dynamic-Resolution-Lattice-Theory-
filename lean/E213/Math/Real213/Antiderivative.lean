import E213.Math.Real213.PhaseCMFinalCapstone

/-!
# Research.Real213Antiderivative

Phase CN: ★ **`IsAntiderivative` class** ★

A function F is an antiderivative of f when F's derivative equals f
(propositionally).  Captures the integration ↔ differentiation
duality in 213-native form.

  IsAntiderivative F sf f := { eq : sf.derivative = f }

Atomic instances:
  id is antiderivative of constant 1
  constant c is antiderivative of constant 0
-/

namespace E213.Math.Real213.Antiderivative

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
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

/-- ★ **IsAntiderivative**: F is differentiable, derivative equals f. -/
structure IsAntiderivative
    (F : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (sF : IsDifferentiable F)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  eq : sF.derivative = f

/-- ★ **PURE pointwise variant**: replaces function-eq `eq` field with
    pointwise `eq_at`.  No funext, no Quot.sound. -/
structure IsAntiderivative_at
    (F : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (sF : IsDifferentiable F)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  eq_at : ∀ x m k, sF.derivative x m k = f x m k

namespace IsAntiderivative

/-- ★ id is antiderivative of constant 1 (= constCutFn (constCut 1 1)). -/
def id_anti : IsAntiderivative id idIsDifferentiable
    (constCutFn (constCut 1 1)) :=
  { eq := rfl }

/-- ★ Constant function c is antiderivative of constant 0. -/
def const_anti (c : Nat → Nat → Bool) :
    IsAntiderivative (constCutFn c) (constIsDifferentiable c)
      (constCutFn (constCut 0 1)) :=
  { eq := rfl }

end IsAntiderivative

namespace IsAntiderivative_at

/-- ★ id_at: id is antiderivative of constant 1 (PURE pointwise). -/
def id_anti_at : IsAntiderivative_at id idIsDifferentiable
    (constCutFn (constCut 1 1)) :=
  { eq_at := fun _ _ _ => rfl }

/-- ★ const_at: constant function c is antiderivative of constant 0. -/
def const_anti_at (c : Nat → Nat → Bool) :
    IsAntiderivative_at (constCutFn c) (constIsDifferentiable c)
      (constCutFn (constCut 0 1)) :=
  { eq_at := fun _ _ _ => rfl }

end IsAntiderivative_at

/-- Phase CN capstone: antiderivative class non-empty. -/
theorem antiderivative_capstone (c : Nat → Nat → Bool) :
    -- (1) id is antiderivative of constant 1
    idIsDifferentiable.derivative = constCutFn (constCut 1 1)
    -- (2) constant c is antiderivative of constant 0
    ∧ (constIsDifferentiable c).derivative = constCutFn (constCut 0 1)
    -- (3) Class non-empty: examples exist
    ∧ ∃ F sF f, IsAntiderivative F sF f :=
  ⟨rfl, rfl,
   ⟨id, idIsDifferentiable, constCutFn (constCut 1 1),
    IsAntiderivative.id_anti⟩⟩

/-- ★ Phase CN _at capstone: pointwise antiderivative class (PURE). -/
theorem antiderivative_capstone_at (c : Nat → Nat → Bool) :
    (∀ x m k, idIsDifferentiable.derivative x m k
                = constCutFn (constCut 1 1) x m k)
    ∧ (∀ x m k, (constIsDifferentiable c).derivative x m k
                = constCutFn (constCut 0 1) x m k)
    ∧ ∃ F sF f, IsAntiderivative_at F sF f :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl,
   ⟨id, idIsDifferentiable, constCutFn (constCut 1 1),
    IsAntiderivative_at.id_anti_at⟩⟩

end E213.Math.Real213.Antiderivative
