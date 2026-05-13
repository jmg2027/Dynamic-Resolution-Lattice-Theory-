import E213.Lib.Math.Analysis.FluxMVT.FluxEquivOps
import E213.Lib.Math.Real213.Mul.CutMulOne

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Mul.CutPow
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Lib.Math.Analysis.FluxMVT.FluxCochain
import E213.Lib.Math.Analysis.FluxMVT.FluxCut
import E213.Lib.Math.Analysis.FluxMVT.FluxDivergence
import E213.Lib.Math.Analysis.FluxMVT.FluxEquiv
import E213.Lib.Math.Analysis.FluxMVT.FluxMVT
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# FluxMVTConcrete
-3: **Concrete MVT** via cohomEquiv.

For specific functions and brackets, the localDivergence cohomEquiv
matches the (scaled) flux of the derivative.  Avoids the "general
MVT" wall by leveraging cutMul_one_one / cutMul_one_const for the
unit bracket case.

  mvt_id_unitBracket    : id at unitBracket — full propEq
  mvt_const_unitBracket : constant function at unitBracket
  mvt_const_balanced    : constant function divergence is balanced (any bracket)
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxMVTConcrete

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Mul.CutPow (cutScale)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Analysis.FluxMVT.FluxCochain.FluxCut
  (fluxAlong isBalanced fluxAlong_const_isBalanced)
open E213.Lib.Math.Analysis.FluxMVT.FluxDivergence.FluxCut
  (fluxScale localDivergence)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Lib.Math.Real213.Mul.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut add neg)
open E213.Lib.Math.Analysis.FluxMVT.FluxEquiv.FluxCut (cohomEquiv cohomEquiv_refl)
open E213.Lib.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence_const_balanced)
open E213.Lib.Math.Analysis.Differentiation.Differentiable (idIsDifferentiable)

namespace FluxCut

/-- MVT for id at unit — forward field pointwise (∅-axiom). -/
theorem mvt_id_unitBracket_forward_at (m k : Nat) :
    (localDivergence id unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMul (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k
  exact cutMul_one_one_at m k

/-- MVT for id at unit — backward field pointwise (∅-axiom). -/
theorem mvt_id_unitBracket_backward_at (m k : Nat) :
    (localDivergence id unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMul (constCut 1 1) (constCut 0 1) m k = constCut 0 1 m k
  exact cutMul_one_const_at 0 1 m k

/-- **MVT for constant at any bracket**: divergence is balanced. -/
theorem mvt_const_balanced (c : Nat → Nat → Bool) (db : DyadicBracket) :
    isBalanced (localDivergence (constCutFn c) db) :=
  localDivergence_const_balanced c db

/-- **Constant function MVT statement**: divergence cohomEquiv to
    a self-equal flux (any cut, since balanced means forward = backward). -/
theorem mvt_const_self_cohomEquiv (c : Nat → Nat → Bool) (db : DyadicBracket) :
    cohomEquiv (localDivergence (constCutFn c) db)
               { forward := (localDivergence (constCutFn c) db).backward,
                 backward := (localDivergence (constCutFn c) db).backward } := by
  refine ⟨?_, ?_⟩
  · intro m k
    exact (mvt_const_balanced c db m k)
  · intro m k
    rfl

/-- **MVT for identity at unitBracket** (fluxCutEq, PURE).
    Built from existing pointwise field theorems. -/
theorem mvt_id_unitBracket_pure :
    E213.Lib.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxCutEq
      (localDivergence id unitBracket) (ofCut (constCut 1 1)) :=
  E213.Lib.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxCutEq_of_pointwise
    mvt_id_unitBracket_forward_at mvt_id_unitBracket_backward_at

/-- ★ MVT corollary for id (fluxCutEq, PURE) — derivative form pointwise. -/
theorem mvt_id_unitBracket_cohomEquiv_pure :
    E213.Lib.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxCutEq
      (localDivergence id unitBracket)
      (ofCut (idIsDifferentiable.derivative (constCut 0 1))) :=
  mvt_id_unitBracket_pure

end FluxCut

end E213.Lib.Math.Analysis.FluxMVT.FluxMVTConcrete
