import E213.Math.Real213.PhaseBACapstone
import E213.Math.Real213.CutSumZero
import E213.Math.Real213.CutMulDetermined

/-!
# Research.Real213FluxMVTPolynomial

Phase BB: MVT for polynomial functions at unitBracket via propEq.

  mvt_square_unitBracket    : localDivergence x² unitBracket = ofCut (1)
  mvt_cube_unitBracket      : localDivergence x³ unitBracket = ofCut (1)

Average rate of x^n over [0,1] = (1-0)/1 = 1, exactly matching what
n·c^(n-1) gives at the MVT point c.
-/

namespace E213.Math.Real213.FluxMVTPolynomial

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul cutMulOuter)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne
  (cutMul_one_one cutMul_one_one_at cutMul_one_const cutMul_one_const_at)
open E213.Math.Real213.FluxMVTConcrete.FluxCut
  (mvt_id_unitBracket mvt_id_unitBracket_pure)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero cutMul_zero_zero_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

namespace FluxCut

/-- **MVT for x² at unitBracket**: localDivergence = ofCut 1 (propEq). -/
theorem mvt_square_unitBracket :
    localDivergence (fun x => cutMul x x) unitBracket
      = ofCut (constCut 1 1) := by
  show ({ forward := cutMul (constCut 1 1)
            (cutMul (constCut 1 1) (constCut 1 1)),
          backward := cutMul (constCut 1 1)
            (cutMul (constCut 0 1) (constCut 0 1)) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_zero_zero,
      cutMul_one_one, cutMul_one_const 0 1]

/-- **MVT for x³ at unitBracket**: localDivergence = ofCut 1 (propEq). -/
theorem mvt_cube_unitBracket :
    localDivergence (fun x => cutMul x (cutMul x x)) unitBracket
      = ofCut (constCut 1 1) := by
  show ({ forward := cutMul (constCut 1 1)
            (cutMul (constCut 1 1)
              (cutMul (constCut 1 1) (constCut 1 1))),
          backward := cutMul (constCut 1 1)
            (cutMul (constCut 0 1)
              (cutMul (constCut 0 1) (constCut 0 1))) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_zero_zero,
      cutMul_one_one, cutMul_zero_zero,
      cutMul_one_one, cutMul_one_const 0 1]

/-- Phase BB capstone: polynomial MVT at unit bracket. -/
theorem polynomial_mvt_unitBracket_capstone :
    localDivergence id unitBracket = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul x x) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul x (cutMul x x)) unitBracket
        = ofCut (constCut 1 1) :=
  ⟨mvt_id_unitBracket, mvt_square_unitBracket, mvt_cube_unitBracket⟩

/-! ### PURE pointwise variants — square + cube via cutMulOuter_congr -/

/-- LD x² at unit forward, pointwise. -/
theorem mvt_square_unitBracket_forward_at (m k : Nat) :
    (localDivergence (fun x => cutMul x x) unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMulOuter (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1)
      (fun _ _ => rfl) (fun m' _ => cutMul_one_one_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- LD x² at unit backward, pointwise. -/
theorem mvt_square_unitBracket_backward_at (m k : Nat) :
    (localDivergence (fun x => cutMul x x) unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMulOuter (constCut 1 1) (cutMul (constCut 0 1) (constCut 0 1))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (constCut 1 1) (cutMul (constCut 0 1) (constCut 0 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (constCut 0 1) (constCut 0 1)) (constCut 0 1)
      (fun _ _ => rfl) (fun m' _ => cutMul_zero_zero_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_const_at 0 1 m k

/-- LD x² at unit (fluxCutEq, PURE). -/
theorem mvt_square_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    mvt_square_unitBracket_forward_at
    mvt_square_unitBracket_backward_at

/-- Helper: fluxAlong x³ at unit forward at point. -/
theorem fluxAlong_cube_unitBracket_forward_at (m k : Nat) :
    cutMul (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1)) m k
      = constCut 1 1 m k := by
  show cutMulOuter (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1)
      (fun _ _ => rfl) (fun m' _ => cutMul_one_one_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- Helper: fluxAlong x³ at unit backward at point. -/
theorem fluxAlong_cube_unitBracket_backward_at (m k : Nat) :
    cutMul (constCut 0 1) (cutMul (constCut 0 1) (constCut 0 1)) m k
      = constCut 0 1 m k := by
  show cutMulOuter (constCut 0 1) (cutMul (constCut 0 1) (constCut 0 1))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (constCut 0 1) (cutMul (constCut 0 1) (constCut 0 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 0 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 0 1) (constCut 0 1)
      (cutMul (constCut 0 1) (constCut 0 1)) (constCut 0 1)
      (fun _ _ => rfl) (fun m' _ => cutMul_zero_zero_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_zero_zero_at m k

/-- LD x³ at unit forward, pointwise. -/
theorem mvt_cube_unitBracket_forward_at (m k : Nat) :
    (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMulOuter (constCut 1 1)
        (cutMul (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1)
        (cutMul (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1)))
      (constCut 1 1)
      (fun _ _ => rfl)
      (fun m' _ => fluxAlong_cube_unitBracket_forward_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- LD x³ at unit backward, pointwise. -/
theorem mvt_cube_unitBracket_backward_at (m k : Nat) :
    (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMulOuter (constCut 1 1)
        (cutMul (constCut 0 1) (cutMul (constCut 0 1) (constCut 0 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (constCut 1 1)
        (cutMul (constCut 0 1) (cutMul (constCut 0 1) (constCut 0 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (constCut 0 1) (cutMul (constCut 0 1) (constCut 0 1)))
      (constCut 0 1)
      (fun _ _ => rfl)
      (fun m' _ => fluxAlong_cube_unitBracket_backward_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_const_at 0 1 m k

/-- LD x³ at unit (fluxCutEq, PURE). -/
theorem mvt_cube_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    mvt_cube_unitBracket_forward_at
    mvt_cube_unitBracket_backward_at

/-- ★ Phase BB capstone (fluxCutEq, PURE): polynomial MVT at unit bracket. -/
theorem polynomial_mvt_unitBracket_capstone_pure :
    fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
        (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
        (ofCut (constCut 1 1)) :=
  ⟨mvt_id_unitBracket_pure, mvt_square_unitBracket_pure,
   mvt_cube_unitBracket_pure⟩

end FluxCut

end E213.Math.Real213.FluxMVTPolynomial
