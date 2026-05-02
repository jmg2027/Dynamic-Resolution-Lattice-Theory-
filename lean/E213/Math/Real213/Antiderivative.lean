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

/-- ★ **IsAntiderivative**: F is differentiable, derivative equals f. -/
structure IsAntiderivative
    (F : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (sF : IsDifferentiable F)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  eq : sF.derivative = f

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

end E213.Math.Real213.Antiderivative
