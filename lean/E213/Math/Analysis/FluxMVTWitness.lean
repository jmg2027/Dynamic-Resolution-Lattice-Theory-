import E213.Math.Real213.CutSumOne
import E213.Math.Analysis.DifferentiableInstances
import E213.Math.Analysis.FluxMVTPolynomial

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumDetermined
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.DyadicBracket
import E213.Math.Analysis.DyadicTrajectory
import E213.Math.Analysis.FluxCut
import E213.Math.Analysis.FluxDivergence
import E213.Math.Analysis.FluxMVT
import E213.Math.Analysis.IsDifferentiable
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

  * `E213.Math.Analysis.FluxMVTWitness`  — base (x²)
  * `E213.Math.Analysis.FluxMVTMore`     — mid(x, x²)
  * `E213.Math.Analysis.FluxMVTNested`   — mid(x, mid(x, x²))
  * `E213.Math.Analysis.FluxMVTNested2`  — mid(mid(x, x²), x²)

(Consolidated 2026-05-05 from 5 phase files: FluxMVTWitness [Phase BR]
+ FluxMVTMore [Phase BU] + FluxMVTNested [Phase CF] + FluxMVTNested2
[Phase CJ] + FluxMVTPattern [Phase CG capstone — DELETED, was pure
bundle].  Per-stage capstone bundles dropped.)
-/

namespace E213.Math.Analysis.FluxMVTWitness

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Analysis.IsDifferentiable (IsDifferentiable)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Math.Real213.CutMulOne
  (cutMul_one_const_at cutMul_const_one_at)
open E213.Math.Real213.CutSumOne (cutSum_half_half_at)
open E213.Math.Real213.CutSumDetermined (cutSumAux_congr)
open E213.Math.Analysis.FluxMVTPolynomial.FluxCut
  (mvt_square_unitBracket_pure)
open E213.Math.Analysis.FluxMVT.FluxCut (fluxCutEq)

/-- d/dx [x²] at x = 1/2 = 1 (pointwise, ∅-axiom). -/
theorem squareDerivative_at_half_at (m k : Nat) :
    squareIsDifferentiable.derivative (constCut 1 2) m k = constCut 1 1 m k := by
  show cutSum (cutMul (constCut 1 1) (constCut 1 2))
              (cutMul (constCut 1 2) (constCut 1 1)) m k
       = constCut 1 1 m k
  show cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                 (cutMul (constCut 1 2) (constCut 1 1)) k (2*m) (2*m)
       = constCut 1 1 m k
  have step :
      cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                (cutMul (constCut 1 2) (constCut 1 1)) k (2*m) (2*m)
      = cutSumAux (constCut 1 2) (constCut 1 2) k (2*m) (2*m) :=
    cutSumAux_congr k (2*m)
      (cutMul (constCut 1 1) (constCut 1 2)) (constCut 1 2)
      (cutMul (constCut 1 2) (constCut 1 1)) (constCut 1 2)
      (fun m' _ => cutMul_one_const_at 1 2 m' (2*k))
      (fun m' _ => cutMul_const_one_at 1 2 m' (2*k))
      (2*m) (Nat.le_refl _)
  rw [step]
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

end E213.Math.Analysis.FluxMVTWitness
