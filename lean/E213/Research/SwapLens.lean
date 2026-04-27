import E213.Hypervisor.Lens
import E213.Research.IdentityLens
import E213.Firmware.Raw.SwapSlash

/-!
# Research.SwapLens: Raw.swap 을 view 로 갖는 Lens

**Lens**: `swapLens : Lens Raw` with `view = Raw.swap`.

swap_slash (Firmware) 가 있어야 증명 가능한 구성.

## 의의

Raw 의 유일한 nontrivial automorphism 이 Lens 의 view 로
실현됨.  idLens (identity) 에 대응하는 "반사 Lens".

## 구조

idLens 와 **같은 combine** (off-diagonal 에서 Raw.slash,
diagonal fallback Raw.a).  **다른 base** (a, b 가 swap).

이는 Raw-matching Lens family 의 한 원소 (RawMatchingLens.lean
일반화).  base 만 swap 해도 view = Raw.swap 이 됨.
-/

namespace E213.Research.SwapLens

open E213.Firmware E213.Hypervisor E213.Research.IdentityLens

/-- Swap Lens: Raw.swap 이 view 인 Lens. -/
def swapLens : Lens Raw where
  base_a := Raw.b
  base_b := Raw.a
  combine x y := if h : x ≠ y then Raw.slash x y h else Raw.a

private theorem swapLens_symmetric :
    ∀ u v : Raw, swapLens.combine u v = swapLens.combine v u :=
  idLens_symmetric

/-- **swapLens.view = Raw.swap**. -/
theorem swapLens_view_eq_swap : ∀ r : Raw, swapLens.view r = Raw.swap r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : swapLens.view (Raw.slash x y h)
                   = swapLens.combine (swapLens.view x) (swapLens.view y) :=
        Raw.fold_slash _ _ _ swapLens_symmetric x y h
      rw [hfs, ihx, ihy]
      have hne : Raw.swap x ≠ Raw.swap y :=
        fun e => h (Raw.swap_injective e)
      show (if h' : Raw.swap x ≠ Raw.swap y then
              Raw.slash (Raw.swap x) (Raw.swap y) h'
            else Raw.a)
           = Raw.swap (Raw.slash x y h)
      rw [dif_pos hne, ← Raw.swap_slash]

/-- Corollary: swapLens.view 는 involutive. -/
theorem swapLens_view_involutive :
    ∀ r : Raw, swapLens.view (swapLens.view r) = r := by
  intro r
  rw [swapLens_view_eq_swap, swapLens_view_eq_swap, Raw.swap_swap]

/-- swapLens 는 injective view (involutive 이므로). -/
theorem swapLens_injective : Function.Injective swapLens.view := by
  intro x y hxy
  rw [swapLens_view_eq_swap, swapLens_view_eq_swap] at hxy
  exact Raw.swap_injective hxy

end E213.Research.SwapLens

namespace E213.Research.SwapLens

open E213.Firmware E213.Hypervisor
open E213.Research.IdentityLens

/-- idLens 와 swapLens 는 refines-equivalent.  둘 다 injective
    이므로 InjectiveLensClass.lean 의 injective_equiv 로부터. -/
theorem idLens_swapLens_refines_equiv :
    idLens.refines swapLens ∧ swapLens.refines idLens := by
  constructor
  · intro x y hxy
    show swapLens.view x = swapLens.view y
    rw [swapLens_view_eq_swap, swapLens_view_eq_swap]
    have h : idLens.view x = idLens.view y := hxy
    rw [idLens_is_id, idLens_is_id] at h
    rw [h]
  · intro x y hxy
    show idLens.view x = idLens.view y
    rw [idLens_is_id, idLens_is_id]
    have h : swapLens.view x = swapLens.view y := hxy
    rw [swapLens_view_eq_swap, swapLens_view_eq_swap] at h
    exact Raw.swap_injective h

end E213.Research.SwapLens
