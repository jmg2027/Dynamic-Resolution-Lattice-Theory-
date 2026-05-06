import E213.Math.Analysis.FluxMVT.FluxMVTWitnessCombinators
import E213.Math.Analysis.DyadicSearch.DyadicRiemann
import E213.Math.Analysis.FluxMVT.FluxMVTWitness
import E213.Math.Analysis.ClassicCalc.ClassicCalcMid
import E213.Math.Analysis.FluxMVT.DyadicMVTWitness

import E213.Math.Real213.Core
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Math.Analysis.Differentiation.DifferentiableMid
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.FluxMVT.FluxCochain
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.FluxMVT.FluxFTC
import E213.Math.Analysis.FluxMVT.FluxFTCPolynomial
import E213.Math.Analysis.FluxMVT.FluxMVT
import E213.Math.Analysis.Differentiation.Differentiable
/-!
# FTC via Riemann sum at unitBracket (depth 0)

The fundamental theorem of calculus connects integration (Riemann
sum) with differentiation:

```
∫_a^b f'(x) dx = f(b) − f(a)
```

For specific witness functions on `[0, 1]`, the depth-0 Riemann sum
of `f.derivative` exactly matches the boundary value `f(1)` —
matching `fluxAlong f unitBracket`.  Witness `c = 1/2` (= unitBracket
midpoint) makes this propositional rather than asymptotic.

## Sub-namespaces (preserved for cross-file `open` declarations)

  * `E213.Math.Analysis.FluxMVT.FTCRiemann`         — id ()
  * `E213.Math.Analysis.FTCRiemannSquare`   — x² ()
  * `E213.Math.Analysis.FTCRiemannMid`      — mid(x, x²) ()
  * `E213.Math.Analysis.FTCRiemannGeneric`  — generic via HasDyadicMVTWitness_at ()

(Consolidated 2026-05-05 from 4 .  FTCRiemannChain
[] was an empty scaffold — DELETED.  Per-stage capstones
dropped.)
-/

namespace E213.Math.Analysis.FluxMVT.FTCRiemann

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Analysis.DyadicSearch.DyadicRiemann
  (riemannSampleSum riemannSampleSum_constCut riemannSampleSum_constCut_at)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Analysis.FluxMVT.FluxFTC.FluxCut (fluxAlong_id_unitBracket)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.Differentiation.Differentiable (idIsDifferentiable)

/-- Riemann sum of id.derivative over unitBracket — pointwise. -/
theorem riemann_id_derivative_unit_at (n : Nat) :
    ∀ m k, riemannSampleSum idIsDifferentiable.derivative unitBracket n m k
            = constCut (2^n * 1) 1 m k :=
  riemannSampleSum_constCut_at 1 1 unitBracket n

/-- Riemann sum of id.derivative at depth 0 = constCut 1 1. -/
theorem riemann_id_derivative_unit_zero :
    riemannSampleSum idIsDifferentiable.derivative unitBracket 0
      = constCut 1 1 := by
  show riemannSampleSum (constCutFn (constCut 1 1)) unitBracket 0
       = constCut 1 1
  rfl

/-- At depth 0, Riemann sum of id.derivative = fluxAlong id (boundary).
    FTC propositionally for id. -/
theorem ftc_riemann_id_depth_zero :
    riemannSampleSum idIsDifferentiable.derivative unitBracket 0
      = (fluxAlong id unitBracket).forward := by
  show constCut 1 1 = constCut 1 1
  rfl

end E213.Math.Analysis.FluxMVT.FTCRiemann

namespace E213.Math.Analysis.FTCRiemannSquare

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.DyadicSearch.DyadicRiemann (riemannSampleSum)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.DyadicSearch.DyadicBracket.DyadicBracket (midCut)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Analysis.Differentiation.Differentiable (IsDifferentiable)
open E213.Math.Analysis.FluxMVT.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Analysis.FluxMVT.FluxFTCPolynomial.FluxCut
  (fluxAlong_square_unitBracket_pure fluxAlong_square_unitBracket_forward_at)
open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

/-- unitBracket midpoint = constCut 1 2 (= 1/2). -/
theorem unitBracket_midCut : unitBracket.midCut = constCut 1 2 := rfl

/-- Riemann sum at depth 0, pointwise. -/
theorem riemann_square_derivative_unit_zero_at (m k : Nat) :
    riemannSampleSum squareIsDifferentiable.derivative unitBracket 0 m k
      = constCut 1 1 m k :=
  squareDerivative_at_half_at m k

/-- FTC-Riemann for x² depth 0, pointwise. -/
theorem ftc_riemann_square_depth_zero_at (m k : Nat) :
    riemannSampleSum squareIsDifferentiable.derivative unitBracket 0 m k
      = (fluxAlong (fun x => cutMul x x) unitBracket).forward m k := by
  rw [riemann_square_derivative_unit_zero_at]
  exact (cutMul_one_one_at m k).symm

end E213.Math.Analysis.FTCRiemannSquare

namespace E213.Math.Analysis.FTCRiemannMid

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.DyadicSearch.DyadicRiemann (riemannSampleSum)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.Differentiation.Differentiable (idIsDifferentiable)
open E213.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Analysis.Differentiation.DifferentiableMid (midIsDifferentiable)
open E213.Math.Analysis.FluxMVTMore (mid_id_square_derivative_at_half_at)

/-- Riemann sum of mid(x, x²)' at unit depth 0, pointwise. -/
theorem riemann_mid_id_square_derivative_zero_at (m k : Nat) :
    riemannSampleSum (midIsDifferentiable idIsDifferentiable
                       squareIsDifferentiable).derivative unitBracket 0 m k
      = constCut 1 1 m k :=
  mid_id_square_derivative_at_half_at m k

end E213.Math.Analysis.FTCRiemannMid

namespace E213.Math.Analysis.FTCRiemannGeneric

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.DyadicSearch.DyadicRiemann (riemannSampleSum)
open E213.Math.Analysis.Differentiation.Differentiable (IsDifferentiable)
open E213.Math.Analysis.DyadicSearch.DyadicBracket.DyadicBracket (midCut)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Analysis.FluxMVT.DyadicMVTWitness (HasDyadicMVTWitness_at)

/-- Generic FTC-Riemann at depth 0 (PURE) via dyadic witness.

  Hypotheses:
    (a) `HasDyadicMVTWitness_at sf` with `witness = unitBracket.midCut` (= 1/2)
    (b) `f` passthrough pointwise (`∀ m k, f(1) m k = constCut 1 1 m k`)

  Conclusion: depth-0 Riemann sum of `sf.derivative` matches `fluxAlong f`
  boundary pointwise. -/
theorem ftc_riemann_generic_via_witness_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (sf : IsDifferentiable f) (w : @HasDyadicMVTWitness_at f sf)
    (h_witness_at_mid : w.witness = unitBracket.midCut)
    (h_pass_one_at : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k)
    (m k : Nat) :
    riemannSampleSum sf.derivative unitBracket 0 m k
      = (fluxAlong f unitBracket).forward m k := by
  show sf.derivative unitBracket.midCut m k = f (constCut 1 1) m k
  rw [← h_witness_at_mid, h_pass_one_at m k]
  exact w.proof_at m k

end E213.Math.Analysis.FTCRiemannGeneric
