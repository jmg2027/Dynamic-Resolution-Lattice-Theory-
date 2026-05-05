import E213.Math.Analysis.FluxMVT.FluxMVTPolynomial
import E213.Math.Real213.CutMulDetermined

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutSumZero
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.FluxMVT.FluxCochain
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.FluxMVT.FluxDivergence
import E213.Math.Analysis.FluxMVT.FluxFTC
import E213.Math.Analysis.FluxMVT.FluxMVT
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

namespace E213.Math.Analysis.FluxMVT.FluxFTCPolynomial

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.FluxMVT.FluxMVTPolynomial.FluxCut
  (mvt_square_unitBracket_pure mvt_cube_unitBracket_pure)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)

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

/-! ### PURE pointwise variants (fluxCutEq form)

Note: full FTC bridge pure variants live downstream
(FluxMVTPassthrough), since this file is upstream and cannot
import FluxMVTPassthrough.  Only the fluxAlong-pure forms are
available here (they use local `_at` field theorems). -/

open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

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

/-- ★ FTC bridge for x² at unit (fluxCutEq, PURE).  Chains
    `mvt_square_pure` with `fluxAlong_square_pure` via fluxBalance_trans. -/
theorem ftc_bridge_square_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (fluxAlong (fun x => cutMul x x) unitBracket) :=
  E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_trans
    mvt_square_unitBracket_pure
    (E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_symm _ _
      fluxAlong_square_unitBracket_pure)

/-- ★ FTC bridge for x³ at unit (fluxCutEq, PURE). -/
theorem ftc_bridge_cube_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
              (fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket) :=
  E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_trans
    mvt_cube_unitBracket_pure
    (E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_symm _ _
      fluxAlong_cube_unitBracket_pure)

/-- ★ Phase BC capstone (fluxCutEq, PURE): polynomial FTC bridges. -/
theorem polynomial_ftc_bridge_capstone_pure :
    fluxCutEq (localDivergence id unitBracket) (fluxAlong id unitBracket)
    ∧ fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
        (fluxAlong (fun x => cutMul x x) unitBracket)
    ∧ fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
        (fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket) :=
  ⟨E213.Math.Analysis.FluxMVT.FluxFTC.FluxCut.ftc_bridge_id_unitBracket_pure,
   ftc_bridge_square_unitBracket_pure,
   ftc_bridge_cube_unitBracket_pure⟩

end FluxCut

end E213.Math.Analysis.FluxMVT.FluxFTCPolynomial
