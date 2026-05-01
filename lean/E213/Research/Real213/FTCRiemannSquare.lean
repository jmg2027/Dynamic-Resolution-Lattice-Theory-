import E213.Research.Real213.PhaseBZMegaOmega

/-!
# Research.Real213FTCRiemannSquare

Phase CA: ★ FTC-Riemann for x² at unitBracket, depth 0 ★

Mathematical: ∫_0^1 (x²)' dx = ∫_0^1 2x dx = 1 = 1² - 0² = (x²)|_0^1.

In framework:
  - depth-0 Riemann sum samples derivative at midpoint = 1/2
  - x²'s derivative at 1/2 = 1 (via squareDerivative_at_half)
  - Hence Riemann sum at depth 0 = constCut 1 1
  - Matches fluxAlong x² unitBracket forward = 1²= 1
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- ★ unitBracket midpoint = constCut 1 2 (= 1/2). -/
theorem unitBracket_midCut : unitBracket.midCut = constCut 1 2 := rfl

/-- ★ Riemann sum of x²'s derivative at unitBracket depth 0 = 1. -/
theorem riemann_square_derivative_unit_zero :
    riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
      = constCut 1 1 := by
  show squareIsDifferentiable.derivative unitBracket.midCut = constCut 1 1
  rw [unitBracket_midCut]
  exact squareDerivative_at_half

/-- ★ FTC-Riemann for x²: depth-0 Riemann sum = boundary value forward. -/
theorem ftc_riemann_square_depth_zero :
    riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
      = (FluxCut.fluxAlong (fun x => cutMul x x) unitBracket).forward := by
  rw [riemann_square_derivative_unit_zero]
  show constCut 1 1 = cutMul (constCut 1 1) (constCut 1 1)
  rw [cutMul_one_one]

/-- Phase CA capstone: FTC-Riemann for x² at unitBracket depth 0. -/
theorem ftc_riemann_square_capstone :
    -- (1) Midpoint sampling: derivative at 1/2 = 1
    riemann_square_derivative_unit_zero ▸ rfl =
        (riemann_square_derivative_unit_zero ▸ rfl :
          riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
            = constCut 1 1)
    -- (2) FTC bridge for x² depth 0
    ∧ riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
        = (FluxCut.fluxAlong (fun x => cutMul x x) unitBracket).forward
    -- (3) fluxAlong x² unitBracket = ofCut 1
    ∧ FluxCut.fluxAlong (fun x => cutMul x x) unitBracket
        = FluxCut.ofCut (constCut 1 1) :=
  ⟨rfl, ftc_riemann_square_depth_zero,
   FluxCut.fluxAlong_square_unitBracket⟩

end E213.Research.Real213.CutSum
