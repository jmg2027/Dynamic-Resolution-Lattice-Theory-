import E213.Math.Real213.FTCRiemannMid

/-!
# Research.Real213FTCRiemannGeneric

Phase CC: ★★ **Generic FTC-Riemann at depth 0** ★★

For any function f with:
  (a) HasDyadicMVTWitness sf with witness = midCut of unitBracket (= 1/2)
  (b) f passthrough (f(0) = 0, f(1) = 1)

we have: depth-0 Riemann sum of f.derivative at unitBracket
matches the boundary value f(1) = constCut 1 1.

Single abstract theorem covering x², mid(x, x²), id ∘ x², etc.
-/

namespace E213.Math.Real213.FTCRiemannGeneric

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)

/-- ★★ **Generic FTC-Riemann at depth 0** via witness at midCut ★★ -/
theorem ftc_riemann_generic_via_witness
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (sf : IsDifferentiable f) (w : @HasDyadicMVTWitness f sf)
    (h_witness_at_mid : w.witness = unitBracket.midCut)
    (h_pass_one : f (constCut 1 1) = constCut 1 1) :
    riemannSampleSum sf.derivative unitBracket 0
      = (FluxCut.fluxAlong f unitBracket).forward := by
  show sf.derivative unitBracket.midCut = f (constCut 1 1)
  rw [h_pass_one]
  rw [← h_witness_at_mid]
  exact w.proof

/-- Phase CC capstone: generic FTC-Riemann at depth 0. -/
theorem ftc_riemann_generic_capstone
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (sf : IsDifferentiable f) (w : @HasDyadicMVTWitness f sf)
    (h_witness_at_mid : w.witness = unitBracket.midCut)
    (h_pass_one : f (constCut 1 1) = constCut 1 1) :
    riemannSampleSum sf.derivative unitBracket 0
      = (FluxCut.fluxAlong f unitBracket).forward :=
  ftc_riemann_generic_via_witness f sf w h_witness_at_mid h_pass_one

/-- Application: x² satisfies the generic FTC-Riemann. -/
theorem ftc_riemann_generic_for_square :
    riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
      = (FluxCut.fluxAlong (fun x => cutMul x x) unitBracket).forward :=
  ftc_riemann_generic_via_witness
    (fun x => cutMul x x) squareIsDifferentiable
    HasDyadicMVTWitness.square rfl cutMul_one_one

end E213.Math.Real213.FTCRiemannGeneric
