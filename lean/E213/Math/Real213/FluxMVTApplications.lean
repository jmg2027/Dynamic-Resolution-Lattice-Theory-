import E213.Math.Real213.FluxMVTPassthrough

/-!
# Research.Real213FluxMVTApplications

Phase BG: applications of passthrough MVT (BF) to derive specific
function MVTs as corollaries.

The earlier polynomial MVT theorems (Phase BB-BE) are NOW recognized
as special cases of the general passthrough theorem.  Same propEq
results, but via structural unification rather than ad-hoc proof.

  mvt_id_via_passthrough         : id passthrough → MVT
  mvt_cutPow_via_passthrough     : cutPow x^(n+1) passthrough → MVT
  mvt_square_via_passthrough     : x² passthrough → MVT
  mvt_cube_via_passthrough       : x³ passthrough → MVT
-/

namespace E213.Math.Real213.FluxMVTApplications

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne (cutMul_one_one cutMul_one_const)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero)
open E213.Math.Real213.CutPowConst (cutPow_one_n cutPow_zero_succ)
open E213.Math.Real213.FluxMVTPassthrough.FluxCut (mvt_passthrough_unit)

namespace FluxCut

/-- id is passthrough: id 0 = 0, id 1 = 1.  Hence MVT via BF. -/
theorem mvt_id_via_passthrough :
    localDivergence id unitBracket = ofCut (constCut 1 1) :=
  mvt_passthrough_unit id rfl rfl

/-- ★ x^(n+1) is passthrough for any n: 0^(n+1) = 0, 1^(n+1) = 1. -/
theorem mvt_cutPow_via_passthrough (n : Nat) :
    localDivergence (fun x => cutPow x (n+1)) unitBracket
      = ofCut (constCut 1 1) :=
  mvt_passthrough_unit (fun x => cutPow x (n+1))
    (cutPow_zero_succ n)
    (cutPow_one_n (n+1))

/-- x² is passthrough → MVT via BF (corollary of generic). -/
theorem mvt_square_via_passthrough :
    localDivergence (fun x => cutMul x x) unitBracket
      = ofCut (constCut 1 1) :=
  mvt_passthrough_unit (fun x => cutMul x x)
    cutMul_zero_zero cutMul_one_one

/-- x³ via passthrough. -/
theorem mvt_cube_via_passthrough :
    localDivergence (fun x => cutMul x (cutMul x x)) unitBracket
      = ofCut (constCut 1 1) :=
  mvt_passthrough_unit (fun x => cutMul x (cutMul x x))
    (by show cutMul (constCut 0 1) (cutMul (constCut 0 1) (constCut 0 1))
        = constCut 0 1
        rw [cutMul_zero_zero, cutMul_zero_zero])
    (by show cutMul (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1))
        = constCut 1 1
        rw [cutMul_one_one, cutMul_one_one])

/-- Phase BG capstone: passthrough applications. -/
theorem passthrough_applications_capstone (n : Nat) :
    localDivergence id unitBracket = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutPow x (n+1)) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul x x) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul x (cutMul x x)) unitBracket
        = ofCut (constCut 1 1) :=
  ⟨mvt_id_via_passthrough, mvt_cutPow_via_passthrough n,
   mvt_square_via_passthrough, mvt_cube_via_passthrough⟩

/-! ### PURE pointwise variants (fluxCutEq form) -/

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Real213.FluxMVTPassthrough.FluxCut (mvt_passthrough_unit_pure)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)
open E213.Math.Real213.CutPowConst (cutPow_one_n_at cutPow_zero_succ_at)

/-- id MVT via passthrough (fluxCutEq, PURE). -/
theorem mvt_id_via_passthrough_pure :
    fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure id (fun _ _ => rfl) (fun _ _ => rfl)

/-- ★ x^(n+1) MVT via passthrough (fluxCutEq, PURE). -/
theorem mvt_cutPow_via_passthrough_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutPow x (n+1))
    (cutPow_zero_succ_at n) (cutPow_one_n_at (n+1))

/-- x² MVT via passthrough (fluxCutEq, PURE). -/
theorem mvt_square_via_passthrough_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutMul x x)
    cutMul_zero_zero_at cutMul_one_one_at

/-- Phase BG capstone (fluxCutEq, PURE). -/
theorem passthrough_applications_capstone_pure (n : Nat) :
    fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
                (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
                (ofCut (constCut 1 1)) :=
  ⟨mvt_id_via_passthrough_pure, mvt_cutPow_via_passthrough_pure n,
   mvt_square_via_passthrough_pure⟩

end FluxCut

end E213.Math.Real213.FluxMVTApplications
