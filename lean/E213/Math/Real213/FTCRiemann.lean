import E213.Math.Real213.FluxMVTWitnessCombinators
import E213.Math.Real213.DyadicRiemann
import E213.Math.Real213.FluxMVTWitness
import E213.Math.Real213.ClassicCalcMid
import E213.Math.Real213.HasDyadicMVTWitness

import E213.Math.Real213.Core
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.DifferentiableInstances
import E213.Math.Real213.DifferentiableMid
import E213.Math.Real213.DyadicBracket
import E213.Math.Real213.DyadicTrajectory
import E213.Math.Real213.FluxCochain
import E213.Math.Real213.FluxCut
import E213.Math.Real213.FluxFTC
import E213.Math.Real213.FluxFTCPolynomial
import E213.Math.Real213.FluxMVT
import E213.Math.Real213.IsDifferentiable
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

  * `E213.Math.Real213.FTCRiemann`         — id (Phase BY)
  * `E213.Math.Real213.FTCRiemannSquare`   — x² (Phase CA)
  * `E213.Math.Real213.FTCRiemannMid`      — mid(x, x²) (Phase CB)
  * `E213.Math.Real213.FTCRiemannGeneric`  — generic via HasDyadicMVTWitness_at (Phase CC)

(Consolidated 2026-05-05 from 4 phase files.  FTCRiemannChain
[Phase CD] was an empty scaffold — DELETED.  Per-stage capstones
dropped.)
-/

namespace E213.Math.Real213.FTCRiemann

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Real213.DyadicRiemann
  (riemannSampleSum riemannSampleSum_constCut riemannSampleSum_constCut_at)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxFTC.FluxCut (fluxAlong_id_unitBracket)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.IsDifferentiable (idIsDifferentiable)

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

end E213.Math.Real213.FTCRiemann

namespace E213.Math.Real213.FTCRiemannSquare

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.DyadicBracket.DyadicBracket (midCut)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.IsDifferentiable (IsDifferentiable)
open E213.Math.Real213.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Real213.FluxFTCPolynomial.FluxCut
  (fluxAlong_square_unitBracket_pure fluxAlong_square_unitBracket_forward_at)
open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

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

end E213.Math.Real213.FTCRiemannSquare

namespace E213.Math.Real213.FTCRiemannMid

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.IsDifferentiable (idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half_at)

/-- Riemann sum of mid(x, x²)' at unit depth 0, pointwise. -/
theorem riemann_mid_id_square_derivative_zero_at (m k : Nat) :
    riemannSampleSum (midIsDifferentiable idIsDifferentiable
                       squareIsDifferentiable).derivative unitBracket 0 m k
      = constCut 1 1 m k :=
  mid_id_square_derivative_at_half_at m k

end E213.Math.Real213.FTCRiemannMid

namespace E213.Math.Real213.FTCRiemannGeneric

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.IsDifferentiable (IsDifferentiable)
open E213.Math.Real213.DyadicBracket.DyadicBracket (midCut)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.HasDyadicMVTWitness (HasDyadicMVTWitness_at)

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

end E213.Math.Real213.FTCRiemannGeneric
