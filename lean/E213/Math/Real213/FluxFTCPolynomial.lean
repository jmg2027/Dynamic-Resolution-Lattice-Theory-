import E213.Math.Real213.FluxMVTPolynomial
import E213.Math.Real213.CutMulDetermined

/-!
# Research.Real213FluxFTCPolynomial

Phase BC: polynomial FTC bridge at unitBracket — propEq form.

For each polynomial at unit bracket, both `localDivergence` and
`fluxAlong` reduce to `ofCut (constCut 1 1)` via `cutMul_one_one` /
`cutMul_zero_zero` cascade.  The framework gives full propositional
equality between rate (divergence) and boundary (flux) forms.

  fluxAlong_square_unitBracket  : flux x² at unit = ofCut 1
  fluxAlong_cube_unitBracket    : flux x³ at unit = ofCut 1
  ftc_bridge_square_unitBracket : LD = fluxAlong (FTC propEq)
  ftc_bridge_cube_unitBracket   : LD = fluxAlong (FTC propEq)
-/

namespace E213.Math.Real213.FluxFTCPolynomial

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.FluxMVTPolynomial.FluxCut
  (mvt_square_unitBracket mvt_cube_unitBracket)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulOne
  (cutMul_one_one cutMul_one_one_at cutMul_one_const)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero cutMul_zero_zero_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Real213.FluxFTC.FluxCut (ftc_bridge_id_unitBracket)

namespace FluxCut

/-- fluxAlong x² at unitBracket forward, pointwise (∅-axiom). -/
theorem fluxAlong_square_unitBracket_forward_at (m k : Nat) :
    (fluxAlong (fun x => cutMul x x) unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k :=
  cutMul_one_one_at m k

/-- fluxAlong x² at unitBracket backward, pointwise (∅-axiom). -/
theorem fluxAlong_square_unitBracket_backward_at (m k : Nat) :
    (fluxAlong (fun x => cutMul x x) unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k :=
  cutMul_zero_zero_at m k

/-- fluxAlong x² at unitBracket = ofCut 1 (function eq). -/
theorem fluxAlong_square_unitBracket :
    fluxAlong (fun x => cutMul x x) unitBracket
      = ofCut (constCut 1 1) := by
  show ({ forward := cutMul (constCut 1 1) (constCut 1 1),
          backward := cutMul (constCut 0 1) (constCut 0 1) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_zero_zero]

/-- fluxAlong x³ at unitBracket forward, pointwise (∅-axiom). -/
theorem fluxAlong_cube_unitBracket_forward_at (m k : Nat) :
    (fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket).forward m k
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
      (fun _ _ => rfl)
      (fun m' _ => cutMul_one_one_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_one_at m k

/-- fluxAlong x³ at unitBracket backward, pointwise (∅-axiom). -/
theorem fluxAlong_cube_unitBracket_backward_at (m k : Nat) :
    (fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
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
      (fun _ _ => rfl)
      (fun m' _ => cutMul_zero_zero_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_zero_zero_at m k

/-- fluxAlong x³ at unitBracket = ofCut 1. -/
theorem fluxAlong_cube_unitBracket :
    fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket
      = ofCut (constCut 1 1) := by
  show ({ forward := cutMul (constCut 1 1)
            (cutMul (constCut 1 1) (constCut 1 1)),
          backward := cutMul (constCut 0 1)
            (cutMul (constCut 0 1) (constCut 0 1)) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_zero_zero, cutMul_one_one, cutMul_zero_zero]

/-- **FTC bridge for x² at unitBracket**: localDivergence = fluxAlong. -/
theorem ftc_bridge_square_unitBracket :
    localDivergence (fun x => cutMul x x) unitBracket
      = fluxAlong (fun x => cutMul x x) unitBracket := by
  rw [mvt_square_unitBracket, fluxAlong_square_unitBracket]

/-- **FTC bridge for x³ at unitBracket**: localDivergence = fluxAlong. -/
theorem ftc_bridge_cube_unitBracket :
    localDivergence (fun x => cutMul x (cutMul x x)) unitBracket
      = fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket := by
  rw [mvt_cube_unitBracket, fluxAlong_cube_unitBracket]

/-- Phase BC capstone: polynomial FTC bridges at unit bracket. -/
theorem polynomial_ftc_bridge_capstone :
    localDivergence id unitBracket = fluxAlong id unitBracket
    ∧ localDivergence (fun x => cutMul x x) unitBracket
        = fluxAlong (fun x => cutMul x x) unitBracket
    ∧ localDivergence (fun x => cutMul x (cutMul x x)) unitBracket
        = fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket :=
  ⟨ftc_bridge_id_unitBracket,
   ftc_bridge_square_unitBracket,
   ftc_bridge_cube_unitBracket⟩

/-! ### PURE pointwise variants (fluxCutEq form)

Note: full FTC bridge pure variants live downstream
(FluxMVTPassthrough), since this file is upstream and cannot
import FluxMVTPassthrough.  Only the fluxAlong-pure forms are
available here (they use local `_at` field theorems). -/

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

/-- fluxAlong x² at unit (fluxCutEq, PURE). -/
theorem fluxAlong_square_unitBracket_pure :
    fluxCutEq (fluxAlong (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    fluxAlong_square_unitBracket_forward_at
    fluxAlong_square_unitBracket_backward_at

/-- fluxAlong x³ at unit (fluxCutEq, PURE). -/
theorem fluxAlong_cube_unitBracket_pure :
    fluxCutEq (fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    fluxAlong_cube_unitBracket_forward_at
    fluxAlong_cube_unitBracket_backward_at

end FluxCut

end E213.Math.Real213.FluxFTCPolynomial
