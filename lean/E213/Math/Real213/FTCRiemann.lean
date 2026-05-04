import E213.Math.Real213.PhaseBXCapstone
import E213.Math.Real213.DyadicRiemann

/-!
# Research.Real213FTCRiemann

Phase BY: ★ FTC via **Riemann sum** for id at unitBracket ★

The fundamental theorem of calculus connects integration (Riemann
sum) with differentiation:

  ∫_a^b f'(x) dx = f(b) - f(a)

For id: f'(x) = 1, so ∫_0^1 1 dx = 1 = id(1) - id(0).

In our framework: `riemannSampleSum id.derivative unitBracket n`
gives `constCut (2^n) 1` (= 2^n unnormalized).  Dividing by 2^n
gives 1, matching `fluxAlong id unitBracket` (boundary).
-/

namespace E213.Math.Real213.FTCRiemann

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Real213.DyadicRiemann
  (riemannSampleSum riemannSampleSum_constCut riemannSampleSum_constCut_at)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxFTC.FluxCut (fluxAlong_id_unitBracket)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.IsDifferentiable (idIsDifferentiable)

/-- ★ Riemann sum of id.derivative over unitBracket — pointwise (PURE). -/
theorem riemann_id_derivative_unit_at (n : Nat) :
    ∀ m k, riemannSampleSum idIsDifferentiable.derivative unitBracket n m k
            = constCut (2^n * 1) 1 m k :=
  riemannSampleSum_constCut_at 1 1 unitBracket n

/-- ★ Riemann sum of id.derivative at depth 0 = constCut 1 1. -/
theorem riemann_id_derivative_unit_zero :
    riemannSampleSum idIsDifferentiable.derivative unitBracket 0
      = constCut 1 1 := by
  show riemannSampleSum (constCutFn (constCut 1 1)) unitBracket 0
       = constCut 1 1
  rfl

/-- ★ At depth 0, Riemann sum of id.derivative equals fluxAlong id
    (boundary value).  This is FTC propositionally for id. -/
theorem ftc_riemann_id_depth_zero :
    riemannSampleSum idIsDifferentiable.derivative unitBracket 0
      = (fluxAlong id unitBracket).forward := by
  show constCut 1 1 = constCut 1 1
  rfl

end E213.Math.Real213.FTCRiemann
