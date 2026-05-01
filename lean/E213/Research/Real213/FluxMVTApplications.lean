import E213.Research.Real213.FluxMVTPassthrough

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

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

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

end FluxCut

end E213.Research.Real213.CutSum
