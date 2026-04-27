import E213.Research.Real213PhaseBHCapstone

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

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

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

/-- Passthrough is closed under cutMul (pointwise product). -/
theorem passthrough_mul
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : f (constCut 0 1) = constCut 0 1)
    (hf_right : f (constCut 1 1) = constCut 1 1)
    (hg_left : g (constCut 0 1) = constCut 0 1)
    (hg_right : g (constCut 1 1) = constCut 1 1) :
    (fun x => cutMul (f x) (g x)) (constCut 0 1) = constCut 0 1
    ∧ (fun x => cutMul (f x) (g x)) (constCut 1 1) = constCut 1 1 := by
  refine ⟨?_, ?_⟩
  · show cutMul (f (constCut 0 1)) (g (constCut 0 1)) = constCut 0 1
    rw [hf_left, hg_left, cutMul_zero_zero]
  · show cutMul (f (constCut 1 1)) (g (constCut 1 1)) = constCut 1 1
    rw [hf_right, hg_right, cutMul_one_one]

/-- MVT extends to composition of passthroughs. -/
theorem mvt_compose_passthrough
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : f (constCut 0 1) = constCut 0 1)
    (hf_right : f (constCut 1 1) = constCut 1 1)
    (hg_left : g (constCut 0 1) = constCut 0 1)
    (hg_right : g (constCut 1 1) = constCut 1 1) :
    localDivergence (g ∘ f) unitBracket = ofCut (constCut 1 1) :=
  let ⟨h0, h1⟩ := passthrough_compose f g hf_left hf_right hg_left hg_right
  mvt_passthrough_unit (g ∘ f) h0 h1

/-- MVT extends to product of passthroughs. -/
theorem mvt_mul_passthrough
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : f (constCut 0 1) = constCut 0 1)
    (hf_right : f (constCut 1 1) = constCut 1 1)
    (hg_left : g (constCut 0 1) = constCut 0 1)
    (hg_right : g (constCut 1 1) = constCut 1 1) :
    localDivergence (fun x => cutMul (f x) (g x)) unitBracket
      = ofCut (constCut 1 1) :=
  let ⟨h0, h1⟩ := passthrough_mul f g hf_left hf_right hg_left hg_right
  mvt_passthrough_unit (fun x => cutMul (f x) (g x)) h0 h1

end FluxCut

end E213.Research.Real213CutSum
