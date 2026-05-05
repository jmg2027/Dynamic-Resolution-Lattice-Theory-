import E213.Math.Analysis.ODE.NewtonFirst

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulDetermined
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumDetermined
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutSumZero
import E213.Math.Analysis.Differentiation.DifferentiableInstances
/-!
# CubeDerivativeAtZero
★ x³ derivative at x = 0 = 0 propEq ★

Math: d/dx [x³] at x = 0 = 3·0² = 0.

In framework: structural reduction via cutMul_zero_zero +
cutMul_one_const + cutSum_zero_zero gives propEq.
-/

namespace E213.Math.Analysis.Differentiation.CubeDerivativeAtZero

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.Differentiation.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable)
open E213.Math.Real213.CutMulOne (cutMul_one_const_at cutMul_const_one_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at cutSum_zero_zero_at)
open E213.Math.Real213.CutSumDetermined (cutSumAux_congr)
open E213.Math.Real213.CutSum (cutSumAux)

/-- ★ d/dx [x²] at x = 0 = 0 pointwise (PURE). -/
theorem squareDerivative_at_zero_at (m k : Nat) :
    squareIsDifferentiable.derivative (constCut 0 1) m k = constCut 0 1 m k := by
  show cutSum (cutMul (constCut 1 1) (constCut 0 1))
              (cutMul (constCut 0 1) (constCut 1 1)) m k = constCut 0 1 m k
  show cutSumAux (cutMul (constCut 1 1) (constCut 0 1))
                 (cutMul (constCut 0 1) (constCut 1 1)) k (2*m) (2*m)
       = constCut 0 1 m k
  have h1 :
      cutSumAux (cutMul (constCut 1 1) (constCut 0 1))
                (cutMul (constCut 0 1) (constCut 1 1)) k (2*m) (2*m)
      = cutSumAux (constCut 0 1) (constCut 0 1) k (2*m) (2*m) :=
    cutSumAux_congr k (2*m)
      (cutMul (constCut 1 1) (constCut 0 1)) (constCut 0 1)
      (cutMul (constCut 0 1) (constCut 1 1)) (constCut 0 1)
      (fun m' _ => cutMul_one_const_at 0 1 m' (2*k))
      (fun m' _ => cutMul_const_one_at 0 1 m' (2*k))
      (2*m) (Nat.le_refl _)
  rw [h1]
  exact cutSum_zero_zero_at m k

/-- ★ d/dx [x³] at x = 0 = 0 pointwise (PURE). -/
theorem cubeDerivative_at_zero_at (m k : Nat) :
    cubeIsDifferentiable.derivative (constCut 0 1) m k = constCut 0 1 m k := by
  show cutSum (cutMul (constCut 1 1) (cutMul (constCut 0 1) (constCut 0 1)))
              (cutMul (constCut 0 1)
                (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                        (cutMul (constCut 0 1) (constCut 1 1)))) m k
       = constCut 0 1 m k
  show cutSumAux
        (cutMul (constCut 1 1) (cutMul (constCut 0 1) (constCut 0 1)))
        (cutMul (constCut 0 1)
          (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                  (cutMul (constCut 0 1) (constCut 1 1))))
        k (2*m) (2*m) = constCut 0 1 m k
  have h1 :
      cutSumAux
          (cutMul (constCut 1 1) (cutMul (constCut 0 1) (constCut 0 1)))
          (cutMul (constCut 0 1)
            (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                    (cutMul (constCut 0 1) (constCut 1 1))))
          k (2*m) (2*m)
      = cutSumAux (constCut 0 1) (constCut 0 1) k (2*m) (2*m) :=
    cutSumAux_congr k (2*m)
      (cutMul (constCut 1 1) (cutMul (constCut 0 1) (constCut 0 1)))
      (constCut 0 1)
      (cutMul (constCut 0 1)
        (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                (cutMul (constCut 0 1) (constCut 1 1))))
      (constCut 0 1)
      (fun m' _ => by
        show cutMul (constCut 1 1) (cutMul (constCut 0 1) (constCut 0 1)) m' (2*k)
              = constCut 0 1 m' (2*k)
        show E213.Math.Real213.CutMul.cutMulOuter (constCut 1 1)
              (cutMul (constCut 0 1) (constCut 0 1))
              (2*k) m' ((m'+1)*((2*k)+1)) ((m'+1)*((2*k)+1))
            = constCut 0 1 m' (2*k)
        have step :
            E213.Math.Real213.CutMul.cutMulOuter (constCut 1 1)
              (cutMul (constCut 0 1) (constCut 0 1))
              (2*k) m' ((m'+1)*((2*k)+1)) ((m'+1)*((2*k)+1))
            = E213.Math.Real213.CutMul.cutMulOuter (constCut 1 1) (constCut 0 1)
              (2*k) m' ((m'+1)*((2*k)+1)) ((m'+1)*((2*k)+1)) :=
          E213.Math.Real213.CutMulDetermined.cutMulOuter_congr
            (2*k) m' ((m'+1)*((2*k)+1)) ((m'+1)*((2*k)+1))
            (constCut 1 1) (constCut 1 1)
            (cutMul (constCut 0 1) (constCut 0 1)) (constCut 0 1)
            (fun _ _ => rfl)
            (fun m'' _ => cutMul_zero_zero_at m'' (2*k))
            ((m'+1)*((2*k)+1)) (Nat.le_refl _)
        rw [step]
        exact cutMul_one_const_at 0 1 m' (2*k))
      (fun m' _ => by
        show cutMul (constCut 0 1)
              (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                      (cutMul (constCut 0 1) (constCut 1 1))) m' (2*k)
            = constCut 0 1 m' (2*k)
        show E213.Math.Real213.CutMul.cutMulOuter (constCut 0 1)
              (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                      (cutMul (constCut 0 1) (constCut 1 1)))
              (2*k) m' ((m'+1)*((2*k)+1)) ((m'+1)*((2*k)+1))
            = constCut 0 1 m' (2*k)
        have step :
            E213.Math.Real213.CutMul.cutMulOuter (constCut 0 1)
              (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                      (cutMul (constCut 0 1) (constCut 1 1)))
              (2*k) m' ((m'+1)*((2*k)+1)) ((m'+1)*((2*k)+1))
            = E213.Math.Real213.CutMul.cutMulOuter (constCut 0 1) (constCut 0 1)
              (2*k) m' ((m'+1)*((2*k)+1)) ((m'+1)*((2*k)+1)) :=
          E213.Math.Real213.CutMulDetermined.cutMulOuter_congr
            (2*k) m' ((m'+1)*((2*k)+1)) ((m'+1)*((2*k)+1))
            (constCut 0 1) (constCut 0 1)
            (cutSum (cutMul (constCut 1 1) (constCut 0 1))
                    (cutMul (constCut 0 1) (constCut 1 1))) (constCut 0 1)
            (fun _ _ => rfl)
            (fun m'' _ => squareDerivative_at_zero_at m'' (2*k))
            ((m'+1)*((2*k)+1)) (Nat.le_refl _)
        rw [step]
        exact cutMul_zero_zero_at m' (2*k))
      (2*m) (Nat.le_refl _)
  rw [h1]
  exact cutSum_zero_zero_at m k

/-- ★ capstone (PURE). -/
theorem polynomial_derivative_at_zero_capstone_at :
    (∀ m k, squareIsDifferentiable.derivative (constCut 0 1) m k
              = constCut 0 1 m k)
    ∧ (∀ m k, cubeIsDifferentiable.derivative (constCut 0 1) m k
                = constCut 0 1 m k) :=
  ⟨squareDerivative_at_zero_at, cubeDerivative_at_zero_at⟩

end E213.Math.Analysis.Differentiation.CubeDerivativeAtZero
