import E213.Research.Real213AntiderivativeCombinators

/-!
# Research.Real213AntiderivativeStructural

Phase CP: ★ structural antiderivative — every IsDifferentiable
yields an IsAntiderivative ★

For any F : Cut → Cut with IsDifferentiable witness sF, the structure
(F, sF, sF.derivative) is an IsAntiderivative trivially via rfl.

This means every smooth function "knows" its derivative, hence
"knows what it integrates to" — the antiderivative class is
fully populated by the differentiable class.

  fromDifferentiable : IsDifferentiable F → IsAntiderivative F _ _
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

namespace IsAntiderivative

/-- ★ Every IsDifferentiable yields an antiderivative of its derivative. -/
def fromDifferentiable {F : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sF : IsDifferentiable F) : IsAntiderivative F sF sF.derivative :=
  { eq := rfl }

/-- Square is antiderivative of (1·x + x·1) = 2x. -/
def square_anti :
    IsAntiderivative (fun x => cutMul x x) squareIsDifferentiable
      (fun x => cutSum (cutMul (constCut 1 1) x) (cutMul x (constCut 1 1))) :=
  fromDifferentiable squareIsDifferentiable

/-- Cube is antiderivative of its formal derivative (= 3x²). -/
def cube_anti :
    IsAntiderivative (fun x => cutMul x (cutMul x x)) cubeIsDifferentiable
      cubeIsDifferentiable.derivative :=
  fromDifferentiable cubeIsDifferentiable

/-- ★ FTC connection: fluxAlong F at unit gives boundary value
    F(1) - F(0) cohomologically. -/
theorem fluxAlong_antiderivative_boundary
    {F sF f} (hF : IsAntiderivative F sF f) :
    FluxCut.fluxAlong F unitBracket
      = { forward := F (constCut 1 1), backward := F (constCut 0 1) } := rfl

end IsAntiderivative

/-- Phase CP capstone: structural antiderivative provides infinite class. -/
theorem antiderivative_structural_capstone :
    -- (1) id antiderivative
    idIsDifferentiable.derivative = constCutFn (constCut 1 1)
    -- (2) Square antiderivative explicit form
    ∧ squareIsDifferentiable.derivative
        = (fun x => cutSum (cutMul (constCut 1 1) x)
                            (cutMul x (constCut 1 1)))
    -- (3) FTC bridge: id at unit
    ∧ FluxCut.fluxAlong id unitBracket = FluxCut.ofCut (constCut 1 1) :=
  ⟨rfl, rfl, FluxCut.fluxAlong_id_unitBracket⟩

end E213.Research.Real213CutSum
