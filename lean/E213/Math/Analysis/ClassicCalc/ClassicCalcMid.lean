import E213.Math.Analysis.FluxMVT.FluxMVTWitness
import E213.Math.Analysis.Differentiation.DifferentiableMid
import E213.Math.Real213.CutMidSelf

import E213.Math.Analysis.ClassicCalc.ClassicCalc
import E213.Math.Real213.Core
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumDetermined
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutSumZero
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.FluxMVT.FluxDivergence
import E213.Math.Analysis.FluxMVT.FluxMVT
import E213.Math.Analysis.FluxMVT.FluxPassthroughClass
/-!
# Research.Real213ClassicCalcMid

Phase BS: Passthrough is closed under midpoint, extending the
calculus-textbook framework to averaged functions.

  Passthrough.mid_pass        : if f, g passthrough, so is mid(f, g)
  ClassicCalc.mid_calc        : ClassicCalc closure under midpoint
  mid_id_square_calc          : mid(id, x²) calc instance
-/

namespace E213.Math.Analysis.ClassicCalc.ClassicCalcMid

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.Differentiation.DifferentiableMid (midIsDifferentiable)

namespace FluxCut.Passthrough_at

open E213.Math.Analysis.FluxMVT.FluxPassthroughClass.FluxCut (Passthrough_at)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Math.Real213.CutSumDetermined (cutSumAux_congr)
open E213.Math.Real213.CutSumZero (cutMid_zero_zero_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut_at)

/-- Midpoint of two passthrough_at's is passthrough_at (PURE).
    Uses cutSumAux_congr to push pointwise pf/pg eq through cutMid
    (= cutHalf ∘ cutSum). -/
def mid_pass {f g} (pf : Passthrough_at f) (pg : Passthrough_at g) :
    Passthrough_at (fun x => cutMid (f x) (g x)) :=
  { left := fun m k => by
      show cutSumAux (f (constCut 0 1)) (g (constCut 0 1))
                     k (2*(2*m)) (2*(2*m)) = constCut 0 1 m k
      have step : cutSumAux (f (constCut 0 1)) (g (constCut 0 1))
                            k (2*(2*m)) (2*(2*m))
                = cutSumAux (constCut 0 1) (constCut 0 1)
                            k (2*(2*m)) (2*(2*m)) :=
        cutSumAux_congr k (2*(2*m))
          (f (constCut 0 1)) (constCut 0 1)
          (g (constCut 0 1)) (constCut 0 1)
          (fun m' _ => pf.left m' (2*k))
          (fun m' _ => pg.left m' (2*k))
          (2*(2*m)) (Nat.le_refl _)
      rw [step]
      exact cutMid_zero_zero_at m k
    right := fun m k => by
      show cutSumAux (f (constCut 1 1)) (g (constCut 1 1))
                     k (2*(2*m)) (2*(2*m)) = constCut 1 1 m k
      have step : cutSumAux (f (constCut 1 1)) (g (constCut 1 1))
                            k (2*(2*m)) (2*(2*m))
                = cutSumAux (constCut 1 1) (constCut 1 1)
                            k (2*(2*m)) (2*(2*m)) :=
        cutSumAux_congr k (2*(2*m))
          (f (constCut 1 1)) (constCut 1 1)
          (g (constCut 1 1)) (constCut 1 1)
          (fun m' _ => pf.right m' (2*k))
          (fun m' _ => pg.right m' (2*k))
          (2*(2*m)) (Nat.le_refl _)
      rw [step]
      exact cutMid_self_constCut_at 1 1 m k (Nat.le_refl _) }

end FluxCut.Passthrough_at

/-! ### ClassicCalc (function-eq) namespace removed (2026-05-XX, part 19)

The function-eq `mid_calc / mid_id_square_calc / mid_square_cube_calc /
mid_id_square_mvt / mid_square_cube_mvt / mid_capstone` were dropped
during the cutEq migration (part 19) because their definitions
inherited funext = Quot.sound from `FluxCut.Passthrough.mid_pass`
(which uses `rw` on function-eq fields).  The PURE `_at` analogues
in the `ClassicCalc_at` namespace below provide the same content
with strict ∅-axiom guarantees.

No downstream consumers existed for the removed identifiers. -/

namespace ClassicCalc_at

open E213.Math.Analysis.ClassicCalc.ClassicCalc (ClassicCalc_at)
open E213.Math.Analysis.ClassicCalc.ClassicCalc.ClassicCalc_at (id_calc square_calc cube_calc)
open E213.Math.Analysis.FluxMVT.FluxPassthroughClass.FluxCut.Passthrough_at (mul_pass)
open E213.Math.Analysis.ClassicCalc.ClassicCalcMid.FluxCut.Passthrough_at
  renaming mid_pass → mid_pass_at

/-- ClassicCalc_at closure under midpoint (PURE pointwise). -/
def mid_calc {f g} (cf : ClassicCalc_at f) (cg : ClassicCalc_at g) :
    ClassicCalc_at (fun x => cutMid (f x) (g x)) :=
  { diff := midIsDifferentiable cf.diff cg.diff
    pass := mid_pass_at (f := f) (g := g) cf.pass cg.pass }

/-- mid(id, x²) ∈ ClassicCalc_at — PURE pointwise. -/
def mid_id_square_calc :
    ClassicCalc_at (fun x => cutMid x (cutMul x x)) :=
  mid_calc id_calc square_calc

/-- mid(x², x³) ∈ ClassicCalc_at — PURE pointwise. -/
def mid_square_cube_calc :
    ClassicCalc_at (fun x => cutMid (cutMul x x) (cutMul x (cutMul x x))) :=
  mid_calc square_calc cube_calc

open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)

/-- mid(x, x²) MVT (fluxCutEq, PURE). -/
theorem mid_id_square_mvt_pure :
    fluxCutEq (localDivergence (fun x => cutMid x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mid_id_square_calc.mvt_pure

/-- mid(x², x³) MVT (fluxCutEq, PURE). -/
theorem mid_square_cube_mvt_pure :
    fluxCutEq (localDivergence (fun x => cutMid (cutMul x x)
                                          (cutMul x (cutMul x x)))
                              unitBracket)
              (ofCut (constCut 1 1)) :=
  mid_square_cube_calc.mvt_pure

/-- Phase BS capstone (fluxCutEq, PURE). -/
theorem mid_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMid x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMid (cutMul x x)
                                            (cutMul x (cutMul x x)))
                                  unitBracket)
                (ofCut (constCut 1 1)) :=
  ⟨mid_id_square_mvt_pure, mid_square_cube_mvt_pure⟩

end ClassicCalc_at

end E213.Math.Analysis.ClassicCalc.ClassicCalcMid
