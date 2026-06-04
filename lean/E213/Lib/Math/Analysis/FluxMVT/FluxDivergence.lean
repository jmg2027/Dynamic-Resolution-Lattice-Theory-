import E213.Lib.Math.Analysis.FluxMVT.FluxCochain
import E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduce
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulDetermined

import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Bisection.CutContinuity
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Mul.CutPow
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Lib.Math.Analysis.FluxMVT.FluxCut
/-!
# FluxDivergence
-3: **Local divergence** = flux per unit measure.

For a dyadic bracket of expE n, measure = 2^(-n), so divergence
= flux × 2^n.  213-native form of *derivative*: cohomological flux
density, no limits, no arithmetic ratio.
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxDivergence

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutPow (cutScale)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Analysis.FluxMVT.FluxCochain.FluxCut
  (fluxAlong isBalanced fluxAlong_const_isBalanced)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)

namespace FluxCut

/-- Scale a flux by a/b (orientation preserved). -/
def fluxScale (a b : Nat) (fc : FluxCut) : FluxCut :=
  { forward := cutScale a b fc.forward,
    backward := cutScale a b fc.backward }

/-- **Local divergence** at a dyadic bracket: flux of f along db,
    scaled by 2^expE (reciprocal of measure).  213-native derivative. -/
def localDivergence (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) : FluxCut :=
  fluxScale (2^db.expE) 1 (fluxAlong f db)

/-- Scaling preserves balance (cohomological vanishing carries through, PURE).
    G110 FLUX-1 template (generic variant). -/
theorem fluxScale_balanced (a b : Nat) (fc : FluxCut) (h : isBalanced fc) :
    isBalanced (fluxScale a b fc) := by
  intro m k
  show cutMul (constCut a b) fc.forward m k
       = cutMul (constCut a b) fc.backward m k
  show E213.Lib.Math.NumberSystems.Real213.Mul.CutMul.cutMulOuter (constCut a b) fc.forward k m
         ((m+1)*(k+1)) ((m+1)*(k+1))
     = E213.Lib.Math.NumberSystems.Real213.Mul.CutMul.cutMulOuter (constCut a b) fc.backward k m
         ((m+1)*(k+1)) ((m+1)*(k+1))
  exact E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduce.cutMulOuter_reduce_at
    (constCut a b) fc.forward (constCut a b) fc.backward m k ((m+1)*(k+1))
    (fun _ _ => rfl) (fun m' _ => h m' k)

/-- Constant function divergence is balanced (∂c = 0). -/
theorem localDivergence_const_balanced (c : Nat → Nat → Bool)
    (db : DyadicBracket) :
    isBalanced (localDivergence (constCutFn c) db) :=
  fluxScale_balanced (2^db.expE) 1 _ (fluxAlong_const_isBalanced c db)

/-- At unitBracket (expE = 0), divergence = flux scaled by 1. -/
theorem localDivergence_unit
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) :
    localDivergence f unitBracket
      = fluxScale 1 1 (fluxAlong f unitBracket) := rfl

/-- Forward of localDivergence = scaled f at right endpoint. -/
theorem localDivergence_forward
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) :
    (localDivergence f db).forward
      = cutScale (2^db.expE) 1 (f db.rightCut) := rfl

/-- Backward of localDivergence = scaled f at left endpoint. -/
theorem localDivergence_backward
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) :
    (localDivergence f db).backward
      = cutScale (2^db.expE) 1 (f db.leftCut) := rfl

end FluxCut

end E213.Lib.Math.Analysis.FluxMVT.FluxDivergence
