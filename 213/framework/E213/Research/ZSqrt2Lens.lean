import E213.Firmware.Raw
import E213.Hypervisor.Lens
import E213.Meta.LensCatalog
import E213.Research.ZSqrt2
import E213.Research.ZSqrt2Domain

/-!
# Research: the `ℤ[√-2]`-Lens (E2 generalisation)

Constructs `z2Lens : Lens Z2` with `base_a = √-2`,
`base_b = -√-2`, `combine = Z2.mul`, and verifies R3
(NonVanishing) and R4 (SwapMatching) in Lean.

Second confirmed counterexample to "R1-R4 force ℂ":
`ℤ[√-2]` is also a countable quadratic extension satisfying
R1-R4 under this Lens.
-/

namespace E213.Research

open E213.Firmware E213.Hypervisor E213.Meta

def z2Lens : Lens Z2 where
  base_a  := Z2.I
  base_b  := Z2.negI
  combine := Z2.mul

example : z2Lens.view Raw.a = Z2.I    := rfl
example : z2Lens.view Raw.b = Z2.negI := rfl

/-- R3 for `z2Lens`: Gaussian-√2 multiplication has no zero
    divisors. -/
theorem z2Lens_nonVanishing : NonVanishing z2Lens := by
  intro u v hu hv
  exact Z2.mul_ne_zero_of_ne_zero hu hv

/-- R4 for `z2Lens`: `Raw.swap` matches `Z2.conj` under view. -/
theorem z2Lens_swapMatching : SwapMatching z2Lens Z2.conj := by
  refine ⟨?_, ?_, ?_⟩
  · intro u; exact Z2.conj_conj u
  · intro h
    have hI : Z2.conj Z2.I = id Z2.I := congrFun h Z2.I
    have himEq : (⟨0, -1⟩ : Z2) = ⟨0, 1⟩ := hI
    have : (-1 : Int) = 1 := (Z2.mk.injEq ..).mp himEq |>.2
    exact absurd this (by decide)
  · intro r
    show Raw.fold Z2.I Z2.negI Z2.mul (Raw.swap r)
       = Z2.conj (Raw.fold Z2.I Z2.negI Z2.mul r)
    exact Raw.fold_swap_hom Z2.I Z2.negI Z2.mul Z2.conj
      Z2.conj_I Z2.conj_negI Z2.conj_mul Z2.mul_comm r

end E213.Research
