import E213.Research.Real213.PhaseBACapstone
import E213.Research.Real213.CutSumZero

/-!
# Research.Real213FluxMVTPolynomial

Phase BB: MVT for polynomial functions at unitBracket via propEq.

  mvt_square_unitBracket    : localDivergence x² unitBracket = ofCut (1)
  mvt_cube_unitBracket      : localDivergence x³ unitBracket = ofCut (1)

Average rate of x^n over [0,1] = (1-0)/1 = 1, exactly matching what
n·c^(n-1) gives at the MVT point c.
-/

namespace E213.Research.Real213.FluxMVTPolynomial

open E213.Firmware E213.Hypervisor

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

end FluxCut

end E213.Research.Real213.FluxMVTPolynomial
