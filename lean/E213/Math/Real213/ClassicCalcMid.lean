import E213.Math.Real213.FluxMVTWitness
import E213.Math.Real213.DifferentiableMid
import E213.Math.Real213.CutMidSelf

/-!
# Research.Real213ClassicCalcMid

Phase BS: Passthrough is closed under midpoint, extending the
calculus-textbook framework to averaged functions.

  Passthrough.mid_pass        : if f, g passthrough, so is mid(f, g)
  ClassicCalc.mid_calc        : ClassicCalc closure under midpoint
  mid_id_square_calc          : mid(id, x²) calc instance
-/

namespace E213.Math.Real213.ClassicCalcMid

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)

namespace FluxCut.Passthrough

/-- Midpoint of two passthroughs is passthrough. -/
def mid_pass {f g} (pf : Passthrough f) (pg : Passthrough g) :
    Passthrough (fun x => cutMid (f x) (g x)) :=
  { left := by
      show cutMid (f (constCut 0 1)) (g (constCut 0 1)) = constCut 0 1
      rw [pf.left, pg.left, cutMid_zero_zero]
    right := by
      show cutMid (f (constCut 1 1)) (g (constCut 1 1)) = constCut 1 1
      rw [pf.right, pg.right]
      exact cutMid_self_constCut 1 1 (by decide) }

end FluxCut.Passthrough

namespace ClassicCalc

/-- ClassicCalc closure under midpoint. -/
def mid_calc {f g} (cf : ClassicCalc f) (cg : ClassicCalc g) :
    ClassicCalc (fun x => cutMid (f x) (g x)) :=
  { diff := midIsDifferentiable cf.diff cg.diff
    pass := FluxCut.Passthrough.mid_pass cf.pass cg.pass }

/-- mid(id, x²) ∈ ClassicCalc — example of new combinator. -/
def mid_id_square_calc :
    ClassicCalc (fun x => cutMid x (cutMul x x)) :=
  mid_calc id_calc square_calc

/-- mid(x², x³) ∈ ClassicCalc. -/
def mid_square_cube_calc :
    ClassicCalc (fun x => cutMid (cutMul x x) (cutMul x (cutMul x x))) :=
  mid_calc square_calc cube_calc

/-- mid(x, x²) MVT propEq. -/
theorem mid_id_square_mvt :
    FluxCut.localDivergence (fun x => cutMid x (cutMul x x)) unitBracket
      = FluxCut.ofCut (constCut 1 1) :=
  mid_id_square_calc.mvt

/-- mid(x², x³) MVT propEq. -/
theorem mid_square_cube_mvt :
    FluxCut.localDivergence (fun x => cutMid (cutMul x x) (cutMul x (cutMul x x)))
                              unitBracket
      = FluxCut.ofCut (constCut 1 1) :=
  mid_square_cube_calc.mvt

/-- Phase BS capstone: midpoint closure adds new MVT instances. -/
theorem mid_capstone :
    FluxCut.localDivergence (fun x => cutMid x (cutMul x x)) unitBracket
        = FluxCut.ofCut (constCut 1 1)
    ∧ FluxCut.localDivergence
        (fun x => cutMid (cutMul x x) (cutMul x (cutMul x x))) unitBracket
        = FluxCut.ofCut (constCut 1 1) :=
  ⟨mid_id_square_mvt, mid_square_cube_mvt⟩

end ClassicCalc

end E213.Math.Real213.ClassicCalcMid
