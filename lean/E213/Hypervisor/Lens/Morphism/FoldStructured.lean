import E213.Hypervisor.LensCore
import E213.Hypervisor.Lens.Initiality

/-!
# FoldStructured: exact characterization of Lens-expressible functions

**Claim**: f : Raw → α is the view of some Lens ↔ f is
**fold-structured** (satisfies the recurrence with base values +
symmetric combine).

## Significance

The central result of this arc.  The exact answer to "which Raw → α
functions are Lens-expressible?"

On the kernel side, `KernelCongruence.lean` covers the equivalence
relation version of the same question (slash-congruence ↔ Lens kernel).
This file is the **function version**.
-/

namespace E213.Hypervisor.Lens.Morphism.FoldStructured

open E213.Firmware E213.Hypervisor E213.Hypervisor.Lens.Initiality

/-- `f : Raw → α` is fold-structured. -/
def FoldStructured {α : Type} (f : Raw → α) : Prop :=
  ∃ (ba bb : α) (c : α → α → α),
    (f Raw.a = ba) ∧ (f Raw.b = bb) ∧
    (∀ u v, c u v = c v u) ∧
    (∀ (x y : Raw) (h : x ≠ y), f (Raw.slash x y h) = c (f x) (f y))

/-- **Forward**: a Lens view is fold-structured. -/
theorem lens_view_fold_structured {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u) :
    FoldStructured L.view := by
  refine ⟨L.base_a, L.base_b, L.combine, rfl, rfl, hsym, ?_⟩
  intro x y h
  exact Raw.fold_slash L.base_a L.base_b L.combine hsym x y h

/-- **Backward**: a fold-structured function is realizable as a Lens view. -/
theorem fold_structured_lens_expressible {α : Type} (f : Raw → α)
    (hfold : FoldStructured f) :
    ∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧ L.view = f := by
  obtain ⟨ba, bb, c, hba, hbb, hsym, hslash⟩ := hfold
  refine ⟨⟨ba, bb, c⟩, hsym, ?_⟩
  funext r
  have := Lens.view_unique (α := α) ⟨ba, bb, c⟩ hsym f hba hbb hslash r
  exact this.symm

end E213.Hypervisor.Lens.Morphism.FoldStructured

namespace E213.Hypervisor.Lens.Morphism.FoldStructured

open E213.Firmware E213.Hypervisor

/-- **Main theorem (iff)**: f is the view of some symmetric-combine Lens
    ↔ f is fold-structured. -/
theorem lens_expressible_iff_fold_structured {α : Type} (f : Raw → α) :
    (∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧ L.view = f)
      ↔ FoldStructured f := by
  constructor
  · intro ⟨L, hsym, hview⟩
    rw [← hview]
    exact lens_view_fold_structured L hsym
  · exact fold_structured_lens_expressible f

end E213.Hypervisor.Lens.Morphism.FoldStructured
