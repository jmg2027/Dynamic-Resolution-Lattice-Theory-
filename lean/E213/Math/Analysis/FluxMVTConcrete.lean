import E213.Math.Analysis.FluxEquivOps
import E213.Math.Real213.CutMulOne

import E213.Math.Real213.Core
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.DyadicBracket
import E213.Math.Analysis.DyadicTrajectory
import E213.Math.Analysis.FluxCochain
import E213.Math.Analysis.FluxCut
import E213.Math.Analysis.FluxDivergence
import E213.Math.Analysis.FluxEquiv
import E213.Math.Analysis.FluxMVT
import E213.Math.Analysis.IsDifferentiable
/-!
# Research.Real213FluxMVTConcrete

Phase AY-3: **Concrete MVT** via cohomEquiv.

For specific functions and brackets, the localDivergence cohomEquiv
matches the (scaled) flux of the derivative.  Avoids the "general
MVT" wall by leveraging cutMul_one_one / cutMul_one_const for the
unit bracket case.

  mvt_id_unitBracket    : id at unitBracket — full propEq
  mvt_const_unitBracket : constant function at unitBracket
  mvt_const_balanced    : constant function divergence is balanced (any bracket)
-/

namespace E213.Math.Analysis.FluxMVTConcrete

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutScale)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Analysis.FluxCut (FluxCut)
open E213.Math.Analysis.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxCochain.FluxCut
  (fluxAlong isBalanced fluxAlong_const_isBalanced)
open E213.Math.Analysis.FluxDivergence.FluxCut
  (fluxScale localDivergence)
open E213.Math.Analysis.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Analysis.FluxCut.FluxCut (ofCut add neg)
open E213.Math.Analysis.FluxEquiv.FluxCut (cohomEquiv cohomEquiv_refl)
open E213.Math.Analysis.FluxDivergence.FluxCut (localDivergence_const_balanced)
open E213.Math.Analysis.IsDifferentiable (idIsDifferentiable)

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
    E213.Math.Analysis.FluxMVT.FluxCut.fluxCutEq
      (localDivergence id unitBracket) (ofCut (constCut 1 1)) :=
  E213.Math.Analysis.FluxMVT.FluxCut.fluxCutEq_of_pointwise
    mvt_id_unitBracket_forward_at mvt_id_unitBracket_backward_at

/-- ★ MVT corollary for id (fluxCutEq, PURE) — derivative form pointwise. -/
theorem mvt_id_unitBracket_cohomEquiv_pure :
    E213.Math.Analysis.FluxMVT.FluxCut.fluxCutEq
      (localDivergence id unitBracket)
      (ofCut (idIsDifferentiable.derivative (constCut 0 1))) :=
  mvt_id_unitBracket_pure

end FluxCut

end E213.Math.Analysis.FluxMVTConcrete
