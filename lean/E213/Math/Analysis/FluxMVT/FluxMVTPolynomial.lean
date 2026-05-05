import E213.Math.Real213.CutSumZero
import E213.Math.Real213.CutMulDetermined
import E213.Math.Real213.CutPowConst

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.FluxMVT.FluxCochain
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.FluxMVT.FluxDivergence
import E213.Math.Analysis.FluxMVT.FluxMVT
import E213.Math.Analysis.FluxMVT.FluxMVTConcrete
/-!
# Polynomial MVT at unitBracket — degrees 2-4 + generic `x^(n+1)`

For polynomial functions on `[0, 1]`, the average rate equals
`(1 - 0)/1 = 1`, exactly matching what `n·c^(n-1)` gives at the MVT
point `c`.  This file packages the propositional MVT/FTC at unit
bracket for the polynomial chain.

| degree   | namespace                                                                            |
|----------|--------------------------------------------------------------------------------------|
| 2, 3     | `E213.Math.Analysis.FluxMVT.FluxMVTPolynomial`  (square + cube)                               |
| 4        | `E213.Math.Analysis.FluxMVTHigh`        (quartic)                                     |
| `n + 1`  | `E213.Math.Analysis.FluxMVTGeneric`     (any polynomial degree, single proof for all) |

Sub-namespaces preserved so external `open … FluxMVTHigh` and
`open … FluxMVTGeneric` declarations stay valid.

(Consolidated 2026-05-05 from 3 phase files: FluxMVTPolynomial
[Phase BB, deg 2-3] + FluxMVTHigh [Phase BD, deg 4] + FluxMVTGeneric
[Phase BE, deg n+1].  Per-stage capstones dropped.)
-/

namespace E213.Math.Analysis.FluxMVT.FluxMVTPolynomial

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul cutMulOuter)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Analysis.FluxMVT.FluxMVTConcrete.FluxCut
  (mvt_id_unitBracket_pure)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

namespace FluxCut

/-- LD x² at unit forward (pointwise). -/
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

/-- LD x² at unit backward (pointwise). -/
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

/-- LD x³ at unit forward (pointwise). -/
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

/-- LD x³ at unit backward (pointwise). -/
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

end FluxCut

end E213.Math.Analysis.FluxMVT.FluxMVTPolynomial

namespace E213.Math.Analysis.FluxMVTHigh

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul cutMulOuter)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

namespace FluxCut

/-- fluxAlong x⁴ at unit forward (pointwise). -/
theorem fluxAlong_quartic_unitBracket_forward_at (m k : Nat) :
    (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      ).forward m k = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMulOuter (cutMul (constCut 1 1) (constCut 1 1))
                   (cutMul (constCut 1 1) (constCut 1 1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (cutMul (constCut 1 1) (constCut 1 1))
                  (cutMul (constCut 1 1) (constCut 1 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1)
      (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1)
      (fun m' _ => cutMul_one_one_at m' k)
      (fun m' _ => cutMul_one_one_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- fluxAlong x⁴ at unit backward (pointwise). -/
theorem fluxAlong_quartic_unitBracket_backward_at (m k : Nat) :
    (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      ).backward m k = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMulOuter (cutMul (constCut 0 1) (constCut 0 1))
                   (cutMul (constCut 0 1) (constCut 0 1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (cutMul (constCut 0 1) (constCut 0 1))
                  (cutMul (constCut 0 1) (constCut 0 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 0 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (cutMul (constCut 0 1) (constCut 0 1)) (constCut 0 1)
      (cutMul (constCut 0 1) (constCut 0 1)) (constCut 0 1)
      (fun m' _ => cutMul_zero_zero_at m' k)
      (fun m' _ => cutMul_zero_zero_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_zero_zero_at m k

/-- fluxAlong x⁴ at unit (fluxCutEq, PURE). -/
theorem fluxAlong_quartic_unitBracket_pure :
    fluxCutEq (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                         unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    fluxAlong_quartic_unitBracket_forward_at
    fluxAlong_quartic_unitBracket_backward_at

/-- LD x⁴ at unit forward (pointwise). -/
theorem mvt_quartic_unitBracket_forward_at (m k : Nat) :
    (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      ).forward m k = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMulOuter (constCut 1 1)
        (cutMul (cutMul (constCut 1 1) (constCut 1 1))
                (cutMul (constCut 1 1) (constCut 1 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1)
        (cutMul (cutMul (constCut 1 1) (constCut 1 1))
                (cutMul (constCut 1 1) (constCut 1 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (cutMul (constCut 1 1) (constCut 1 1))
              (cutMul (constCut 1 1) (constCut 1 1))) (constCut 1 1)
      (fun _ _ => rfl)
      (fun m' _ => fluxAlong_quartic_unitBracket_forward_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- LD x⁴ at unit backward (pointwise). -/
theorem mvt_quartic_unitBracket_backward_at (m k : Nat) :
    (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      ).backward m k = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMulOuter (constCut 1 1)
        (cutMul (cutMul (constCut 0 1) (constCut 0 1))
                (cutMul (constCut 0 1) (constCut 0 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (constCut 1 1)
        (cutMul (cutMul (constCut 0 1) (constCut 0 1))
                (cutMul (constCut 0 1) (constCut 0 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (cutMul (constCut 0 1) (constCut 0 1))
              (cutMul (constCut 0 1) (constCut 0 1))) (constCut 0 1)
      (fun _ _ => rfl)
      (fun m' _ => fluxAlong_quartic_unitBracket_backward_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_const_at 0 1 m k

/-- LD x⁴ at unit (fluxCutEq, PURE). -/
theorem mvt_quartic_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                                unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    mvt_quartic_unitBracket_forward_at
    mvt_quartic_unitBracket_backward_at

/-- FTC bridge for x⁴ at unit (fluxCutEq, PURE). -/
theorem ftc_bridge_quartic_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                                unitBracket)
              (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                          unitBracket) :=
  E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_trans
    mvt_quartic_unitBracket_pure
    (E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_symm _ _
      fluxAlong_quartic_unitBracket_pure)

end FluxCut

end E213.Math.Analysis.FluxMVTHigh

namespace E213.Math.Analysis.FluxMVTGeneric

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutPowConst (cutPow_one_n_at cutPow_zero_succ_at)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

namespace FluxCut

/-- Generic MVT for x^(n+1) at unit forward (pointwise). -/
theorem mvt_cutPow_unitBracket_forward_at (n m k : Nat) :
    (localDivergence (fun x => cutPow x (n+1)) unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMul (constCut 1 1) (cutPow (constCut 1 1) (n+1)) m k
       = constCut 1 1 m k
  show cutMulOuter (constCut 1 1) (cutPow (constCut 1 1) (n+1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1) (cutPow (constCut 1 1) (n+1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutPow (constCut 1 1) (n+1)) (constCut 1 1)
      (fun _ _ => rfl)
      (fun m' _ => cutPow_one_n_at (n+1) m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_one_at m k

/-- Generic MVT for x^(n+1) at unit backward (pointwise). -/
theorem mvt_cutPow_unitBracket_backward_at (n m k : Nat) :
    (localDivergence (fun x => cutPow x (n+1)) unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMul (constCut 1 1) (cutPow (constCut 0 1) (n+1)) m k
       = constCut 0 1 m k
  show cutMulOuter (constCut 1 1) (cutPow (constCut 0 1) (n+1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (constCut 1 1) (cutPow (constCut 0 1) (n+1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutPow (constCut 0 1) (n+1)) (constCut 0 1)
      (fun _ _ => rfl)
      (fun m' _ => cutPow_zero_succ_at n m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_const_at 0 1 m k

/-- fluxAlong x^(n+1) at unit forward (pointwise). -/
theorem fluxAlong_cutPow_unitBracket_forward_at (n m k : Nat) :
    (fluxAlong (fun x => cutPow x (n+1)) unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k :=
  cutPow_one_n_at (n+1) m k

/-- fluxAlong x^(n+1) at unit backward (pointwise). -/
theorem fluxAlong_cutPow_unitBracket_backward_at (n m k : Nat) :
    (fluxAlong (fun x => cutPow x (n+1)) unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k :=
  cutPow_zero_succ_at n m k

/-- Generic MVT for x^(n+1) at unit (fluxCutEq, PURE). -/
theorem mvt_cutPow_unitBracket_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    (mvt_cutPow_unitBracket_forward_at n)
    (mvt_cutPow_unitBracket_backward_at n)

/-- Generic fluxAlong for x^(n+1) at unit (fluxCutEq, PURE). -/
theorem fluxAlong_cutPow_unitBracket_pure (n : Nat) :
    fluxCutEq (fluxAlong (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    (fluxAlong_cutPow_unitBracket_forward_at n)
    (fluxAlong_cutPow_unitBracket_backward_at n)

/-- Generic FTC bridge for x^(n+1) at unit (fluxCutEq, PURE). -/
theorem ftc_bridge_cutPow_unitBracket_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (fluxAlong (fun x => cutPow x (n+1)) unitBracket) :=
  E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_trans
    (mvt_cutPow_unitBracket_pure n)
    (E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_symm _ _
      (fluxAlong_cutPow_unitBracket_pure n))

end FluxCut

end E213.Math.Analysis.FluxMVTGeneric
