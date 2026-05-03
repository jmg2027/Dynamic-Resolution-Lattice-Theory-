import E213.Math.Real213.PhaseBZMegaOmega

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

namespace E213.Math.Real213.FTCRiemannSquare

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.DyadicBracket.DyadicBracket (midCut)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.IsDifferentiable (IsDifferentiable)
open E213.Math.Real213.FluxMVTWitness
  (squareDerivative_at_half squareDerivative_at_half_at)
open E213.Math.Real213.CutMulOne (cutMul_one_one cutMul_one_one_at)
open E213.Math.Real213.FluxFTCPolynomial.FluxCut
  (fluxAlong_square_unitBracket fluxAlong_square_unitBracket_pure
   fluxAlong_square_unitBracket_forward_at)
open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

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
      = (fluxAlong (fun x => cutMul x x) unitBracket).forward := by
  rw [riemann_square_derivative_unit_zero]
  show constCut 1 1 = cutMul (constCut 1 1) (constCut 1 1)
  rw [cutMul_one_one]

/-! ### PURE pointwise variants (∅-axiom) -/

/-- ★ Riemann sum at depth 0, pointwise (PURE). -/
theorem riemann_square_derivative_unit_zero_at (m k : Nat) :
    riemannSampleSum squareIsDifferentiable.derivative unitBracket 0 m k
      = constCut 1 1 m k :=
  squareDerivative_at_half_at m k

/-- ★ FTC-Riemann for x² depth 0, pointwise (PURE). -/
theorem ftc_riemann_square_depth_zero_at (m k : Nat) :
    riemannSampleSum squareIsDifferentiable.derivative unitBracket 0 m k
      = (fluxAlong (fun x => cutMul x x) unitBracket).forward m k := by
  rw [riemann_square_derivative_unit_zero_at]
  exact (cutMul_one_one_at m k).symm

/-- Phase CA capstone: FTC-Riemann for x² at unitBracket depth 0. -/
theorem ftc_riemann_square_capstone :
    -- (1) Midpoint sampling: derivative at 1/2 = 1
    riemann_square_derivative_unit_zero ▸ rfl =
        (riemann_square_derivative_unit_zero ▸ rfl :
          riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
            = constCut 1 1)
    -- (2) FTC bridge for x² depth 0
    ∧ riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
        = (fluxAlong (fun x => cutMul x x) unitBracket).forward
    -- (3) fluxAlong x² unitBracket = ofCut 1
    ∧ fluxAlong (fun x => cutMul x x) unitBracket
        = ofCut (constCut 1 1) :=
  ⟨rfl, ftc_riemann_square_depth_zero,
   fluxAlong_square_unitBracket⟩

/-- ★ Phase CA capstone (PURE) — pointwise FTC-Riemann + fluxAlong. -/
theorem ftc_riemann_square_capstone_pure :
    (∀ m k, riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
              m k = constCut 1 1 m k)
    ∧ (∀ m k, riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
                m k
              = (fluxAlong (fun x => cutMul x x) unitBracket).forward m k)
    ∧ fluxCutEq (fluxAlong (fun x => cutMul x x) unitBracket)
                (ofCut (constCut 1 1)) :=
  ⟨riemann_square_derivative_unit_zero_at,
   ftc_riemann_square_depth_zero_at,
   fluxAlong_square_unitBracket_pure⟩

end E213.Math.Real213.FTCRiemannSquare
