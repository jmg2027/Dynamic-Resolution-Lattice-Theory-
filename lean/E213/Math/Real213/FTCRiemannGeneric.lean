import E213.Math.Real213.FTCRiemannMid

/-!
# Research.Real213FTCRiemannGeneric

Phase CC: ★★ **Generic FTC-Riemann at depth 0** ★★ — PURE pointwise.

For any function f with:
  (a) HasDyadicMVTWitness_at sf with witness = midCut of unitBracket (= 1/2)
  (b) f passthrough pointwise (∀ m k, f(1) m k = constCut 1 1 m k)

we have: depth-0 Riemann sum of f.derivative at unitBracket
matches the boundary value f(1) pointwise.

(Function-eq facade was deleted 2026-05-XX session 27.)
-/

namespace E213.Math.Real213.FTCRiemannGeneric

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicRiemann (riemannSampleSum)
open E213.Math.Real213.IsDifferentiable (IsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.DyadicBracket.DyadicBracket (midCut)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.HasDyadicMVTWitness (HasDyadicMVTWitness_at)

/-- ★★ **Generic FTC-Riemann at depth 0 (PURE)** via _at witness ★★ -/
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
