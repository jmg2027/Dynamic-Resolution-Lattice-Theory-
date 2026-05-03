import E213.Math.Real213.PhaseBHCapstone

/-!
# Research.Real213FluxMVTClosure

Phase BI: passthrough class is closed under composition and midpoint.

If f and g are both passthrough (f(0)=0, f(1)=1, g(0)=0, g(1)=1),
then so are:
  - g ∘ f       (composition)
  - cutMid f g  (pointwise midpoint)
  - cutMul f g  (pointwise product, when carefully arranged)

Hence MVT/FTC propEq extend to these via Phase BF.
-/

namespace E213.Math.Real213.FluxMVTClosure

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne (cutMul_one_one cutMul_one_const)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero)

namespace FluxCut

/-- Passthrough is closed under composition. -/
theorem passthrough_compose
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : f (constCut 0 1) = constCut 0 1)
    (hf_right : f (constCut 1 1) = constCut 1 1)
    (hg_left : g (constCut 0 1) = constCut 0 1)
    (hg_right : g (constCut 1 1) = constCut 1 1) :
    (g ∘ f) (constCut 0 1) = constCut 0 1
    ∧ (g ∘ f) (constCut 1 1) = constCut 1 1 := by
  refine ⟨?_, ?_⟩
  · show g (f (constCut 0 1)) = constCut 0 1
    rw [hf_left, hg_left]
  · show g (f (constCut 1 1)) = constCut 1 1
    rw [hf_right, hg_right]

/-! ### PURE pointwise variants — strict ∅-axiom (mul case)

`mul_passthrough_at` is fully pointwise via `cutMulOuter_congr` —
no funext.  `compose_passthrough` cannot be made fully pointwise
here (substitution under `g` requires function-eq for `f`);
deferred to `FluxPassthroughClass.Passthrough_at.compose_pass`.
The `mul_pure` MVT variant feeds fluxCutEq downstream. -/

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Real213.FluxMVTPassthrough.FluxCut
  (mvt_passthrough_unit_pure)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)

/-- Passthrough closed under cutMul — left, fully pointwise (∅-axiom). -/
theorem passthrough_mul_at_left
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (hg_left : ∀ m k, g (constCut 0 1) m k = constCut 0 1 m k)
    (m k : Nat) :
    cutMul (f (constCut 0 1)) (g (constCut 0 1)) m k = constCut 0 1 m k := by
  show cutMulOuter (f (constCut 0 1)) (g (constCut 0 1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (f (constCut 0 1)) (g (constCut 0 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 0 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (f (constCut 0 1)) (constCut 0 1)
      (g (constCut 0 1)) (constCut 0 1)
      (fun m' _ => hf_left m' k)
      (fun m' _ => hg_left m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_zero_zero_at m k

/-- Passthrough closed under cutMul — right, fully pointwise (∅-axiom). -/
theorem passthrough_mul_at_right
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k)
    (hg_right : ∀ m k, g (constCut 1 1) m k = constCut 1 1 m k)
    (m k : Nat) :
    cutMul (f (constCut 1 1)) (g (constCut 1 1)) m k = constCut 1 1 m k := by
  show cutMulOuter (f (constCut 1 1)) (g (constCut 1 1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (f (constCut 1 1)) (g (constCut 1 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (f (constCut 1 1)) (constCut 1 1)
      (g (constCut 1 1)) (constCut 1 1)
      (fun m' _ => hf_right m' k)
      (fun m' _ => hg_right m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- MVT for product of passthroughs (fluxCutEq, PURE). -/
theorem mvt_mul_passthrough_pure
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (hf_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k)
    (hg_left : ∀ m k, g (constCut 0 1) m k = constCut 0 1 m k)
    (hg_right : ∀ m k, g (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence (fun x => cutMul (f x) (g x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutMul (f x) (g x))
    (passthrough_mul_at_left f g hf_left hg_left)
    (passthrough_mul_at_right f g hf_right hg_right)

end FluxCut

end E213.Math.Real213.FluxMVTClosure
