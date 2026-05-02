import E213.Math.Real213.FluxMVTPolynomial

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

namespace FluxCut

/-- fluxAlong x² at unitBracket = ofCut 1. -/
theorem fluxAlong_square_unitBracket :
    fluxAlong (fun x => cutMul x x) unitBracket
      = ofCut (constCut 1 1) := by
  show ({ forward := cutMul (constCut 1 1) (constCut 1 1),
          backward := cutMul (constCut 0 1) (constCut 0 1) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_zero_zero]

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

end FluxCut

end E213.Math.Real213.FluxFTCPolynomial
