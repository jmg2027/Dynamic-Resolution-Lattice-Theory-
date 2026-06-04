import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumOne
import E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Lib.Math.Analysis.FluxMVT.FluxMVTPolynomial
import E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum

import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMulOne
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumDetermined
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Lib.Math.Analysis.FluxMVT.FluxCut
import E213.Lib.Math.Analysis.FluxMVT.FluxDivergence
import E213.Lib.Math.Analysis.FluxMVT.FluxMVT
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# Constructive dyadic MVT witnesses at `c = 1/2`

Functions buildable from `{id, x², mid}` combinators all admit a
*dyadic* (constructively rational) witness for the Mean Value Theorem
at the point `c = 1/2 = constCut 1 2`.  Key reduction: `cutMid X X = X`
for constant cuts, plus the constCut algebra of cutSum/cutMul.

| function                            | witness | derivative at 1/2 |
|-------------------------------------|---------|-------------------|
| `x²`                                | 1/2     | 1                 |
| `mid(x, x²) = (x+x²)/2`             | 1/2     | 1                 |
| `mid(x, mid(x, x²)) = (3x+x²)/4`    | 1/2     | 1                 |
| `mid(mid(x,x²), x²) = (x+3x²)/4`    | 1/2     | 1                 |

Sub-namespaces preserved (cross-file `open` declarations stay valid):

  * `E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness`  — base (x²)
  * `E213.Lib.Math.Analysis.FluxMVTMore`     — mid(x, x²)
  * `E213.Lib.Math.Analysis.FluxMVTNested`   — mid(x, mid(x, x²))
  * `E213.Lib.Math.Analysis.FluxMVTNested2`  — mid(mid(x, x²), x²)

( from 5 FluxMVTWitness []
+ FluxMVTMore [] + FluxMVTNested [] + FluxMVTNested2
[] + FluxMVTPattern [capstone — DELETED, was pure
bundle].  Per-stage capstone bundles dropped.)
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness

open E213.Theory E213.Lens
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.Differentiable (IsDifferentiable)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSumAux)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMulOne
  (cutMul_one_const_at cutMul_const_one_at)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumOne (cutSum_half_half_at)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumDetermined (cutSumAux_congr)
open E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum
  (cutSumAux_unitBracket_reduce_at)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVTPolynomial.FluxCut
  (mvt_square_unitBracket_pure)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq)

/-- d/dx [x²] at x = 1/2 = 1 (pointwise, ∅-axiom).
    G110 FLUX-1 sum template. -/
theorem squareDerivative_at_half_at (m k : Nat) :
    squareIsDifferentiable.derivative (constCut 1 2) m k = constCut 1 1 m k := by
  show cutSum (cutMul (constCut 1 1) (constCut 1 2))
              (cutMul (constCut 1 2) (constCut 1 1)) m k
       = constCut 1 1 m k
  show cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                 (cutMul (constCut 1 2) (constCut 1 1)) k (2*m) (2*m)
       = constCut 1 1 m k
  rw [cutSumAux_unitBracket_reduce_at
        (cutMul (constCut 1 1) (constCut 1 2))
        (cutMul (constCut 1 2) (constCut 1 1))
        (constCut 1 2) (constCut 1 2) k (2*m)
        (fun m' _ => cutMul_one_const_at 1 2 m' (2*k))
        (fun m' _ => cutMul_const_one_at 1 2 m' (2*k))]
  exact cutSum_half_half_at m k

/-- The witness c = 1/2 is interior to [0, 1]. -/
theorem mvt_square_witness_in_interior :
    (constCut 1 2 : Nat → Nat → Bool) 1 2 = true := by decide

/-- MVT for x² with explicit dyadic witness c = 1/2 (PURE). -/
theorem mvt_square_explicit_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1))
    ∧ (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
                = constCut 1 1 m k) :=
  ⟨mvt_square_unitBracket_pure, squareDerivative_at_half_at⟩

/-- MVT existence (pointwise) with explicit witness for x² (PURE). -/
theorem mvt_square_explicit_witness_at :
    ∃ c, ∀ m k, squareIsDifferentiable.derivative c m k = constCut 1 1 m k :=
  ⟨constCut 1 2, squareDerivative_at_half_at⟩

end E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness
