import E213.Math.Real213.NewtonFirst

/-!
# Research.Real213CubeDerivativeAtZero

Phase CY: ★ x³ derivative at x = 0 = 0 propEq ★

Math: d/dx [x³] at x = 0 = 3·0² = 0.

In framework: structural reduction via cutMul_zero_zero +
cutMul_one_const + cutSum_zero_zero gives propEq.
-/

namespace E213.Math.Real213.CubeDerivativeAtZero

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)

/-- ★ d/dx [x³] at x = 0 = 0 (propEq via structural reduction). -/
theorem cubeDerivative_at_zero :
    cubeIsDifferentiable.derivative (constCut 0 1) = constCut 0 1 := by
  show cutSum (cutMul (constCut 1 1) (cutMul (constCut 0 1) (constCut 0 1)))
              (cutMul (constCut 0 1)
                (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                        (cutMul (constCut 0 1) (constCut 1 1))))
       = constCut 0 1
  simp only [cutMul_zero_zero, cutMul_one_const, cutMul_const_one,
             cutSum_zero_zero]

/-- ★ d/dx [x⁴] at x = 0 = 0. -/
theorem quarticDerivative_at_zero :
    quarticIsDifferentiable.derivative (constCut 0 1) = constCut 0 1 := by
  show cutSum (cutMul (squareIsDifferentiable.derivative (constCut 0 1))
                      (cutMul (constCut 0 1) (constCut 0 1)))
              (cutMul (cutMul (constCut 0 1) (constCut 0 1))
                      (squareIsDifferentiable.derivative (constCut 0 1)))
       = constCut 0 1
  show cutSum (cutMul (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                              (cutMul (constCut 0 1) (constCut 1 1)))
                      (cutMul (constCut 0 1) (constCut 0 1)))
              (cutMul (cutMul (constCut 0 1) (constCut 0 1))
                      (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                              (cutMul (constCut 0 1) (constCut 1 1))))
       = constCut 0 1
  simp only [cutMul_zero_zero, cutMul_one_const, cutMul_const_one,
             cutSum_zero_zero]

/-- Phase CY capstone: polynomial derivatives at x = 0 propEq. -/
theorem polynomial_derivative_at_zero_capstone :
    -- d/dx [x²] at 0 = 0 (already proven in BR via cutMul reduction)
    squareIsDifferentiable.derivative (constCut 0 1) = constCut 0 1
    -- d/dx [x³] at 0 = 0
    ∧ cubeIsDifferentiable.derivative (constCut 0 1) = constCut 0 1
    -- d/dx [x⁴] at 0 = 0
    ∧ quarticIsDifferentiable.derivative (constCut 0 1) = constCut 0 1 := by
  refine ⟨?_, cubeDerivative_at_zero, quarticDerivative_at_zero⟩
  show cutSum (cutMul (constCut 1 1) (constCut 0 1))
              (cutMul (constCut 0 1) (constCut 1 1)) = constCut 0 1
  simp only [cutMul_one_const, cutMul_const_one, cutSum_zero_zero]

end E213.Math.Real213.CubeDerivativeAtZero
