import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.Instances.Identity

/-!
# SwapLens: Lens with Raw.swap as its view

**Lens**: `swapLens : Lens Raw` with `view = Raw.swap`.

Construction is only provable with swap_slash (via Theory.Raw).

## Significance

The unique nontrivial automorphism of Raw is realized as the view of a Lens.
The "reflection Lens" corresponding to idLens (identity).

## Structure

**Same combine** as idLens (Raw.slash off-diagonal, Raw.a diagonal fallback).
**Different base** (a, b swapped).

This is one element of the Raw-matching Lens family (generalized in
RawMatchingLens.lean).  Swapping just the base yields view = Raw.swap.
-/

namespace E213.Lens.Instances.Swap

open E213.Theory E213.Lens E213.Lens.Instances.Identity

/-- Swap Lens: Lens whose view is Raw.swap. -/
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

/-- Corollary: swapLens.view is involutive. -/
theorem swapLens_view_involutive :
    ∀ r : Raw, swapLens.view (swapLens.view r) = r := by
  intro r
  rw [swapLens_view_eq_swap, swapLens_view_eq_swap, Raw.swap_swap]

/-- swapLens has an injective view (since it is involutive). -/
theorem swapLens_injective : Function.Injective swapLens.view := by
  intro x y hxy
  rw [swapLens_view_eq_swap, swapLens_view_eq_swap] at hxy
  exact Raw.swap_injective hxy


open E213.Theory E213.Lens
open E213.Lens.Instances.Identity

/-- idLens and swapLens are refines-equivalent.  Both are injective,
    so this follows from injective_equiv in InjectiveLensClass.lean. -/
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

end E213.Lens.Instances.Swap
