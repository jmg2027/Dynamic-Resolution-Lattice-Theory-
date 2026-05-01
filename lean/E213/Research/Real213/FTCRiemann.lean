import E213.Research.Real213.PhaseBXCapstone
import E213.Research.Real213.DyadicRiemann

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

namespace E213.Research.Real213.FTCRiemann

open E213.Firmware E213.Hypervisor

/-- ★ Riemann sum of id.derivative over unitBracket = constCut (2^n · 1) 1. -/
theorem riemann_id_derivative_unit (n : Nat) :
    riemannSampleSum idIsDifferentiable.derivative unitBracket n
      = constCut (2^n * 1) 1 := by
  show riemannSampleSum (constCutFn (constCut 1 1)) unitBracket n
       = constCut (2^n * 1) 1
  exact riemannSampleSum_constCut 1 1 unitBracket n

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
      = (FluxCut.fluxAlong id unitBracket).forward := by
  show constCut 1 1 = constCut 1 1
  rfl

/-- Phase BY capstone: FTC-Riemann connection for id at depth 0. -/
theorem ftc_riemann_capstone :
    -- (1) Riemann sum closed form (∀ n)
    (∀ n, riemannSampleSum idIsDifferentiable.derivative unitBracket n
            = constCut (2^n * 1) 1)
    -- (2) At depth 0: matches fluxAlong forward (FTC propEq)
    ∧ riemannSampleSum idIsDifferentiable.derivative unitBracket 0
        = (FluxCut.fluxAlong id unitBracket).forward
    -- (3) fluxAlong id unitBracket = ofCut (constCut 1 1)
    ∧ FluxCut.fluxAlong id unitBracket
        = FluxCut.ofCut (constCut 1 1) :=
  ⟨riemann_id_derivative_unit,
   ftc_riemann_id_depth_zero,
   FluxCut.fluxAlong_id_unitBracket⟩

end E213.Research.Real213.FTCRiemann
