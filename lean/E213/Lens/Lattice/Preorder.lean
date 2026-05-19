import E213.Lens.LensCore

/-!
# RefinesPreorder: preorder structure of Lens.refines

Explicit theorems for the preorder claim in PAPER1 §3.3:
reflexivity + transitivity.
-/

namespace E213.Lens.Lattice.Preorder

open E213.Theory E213.Lens

/-- Reflexivity. -/
theorem refines_refl {α : Type} (L : Lens α) : L.refines L := by
  intro x y h; exact h

/-- Transitivity. -/
theorem refines_trans {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (h1 : L.refines M) (h2 : M.refines N) : L.refines N := by
  intro x y h; exact h2 x y (h1 x y h)

/-- **Antisymmetry at the kernel level**: if L and M refine each
    other, their equivalence kernels coincide.  Two lenses related
    by mutual refinement have identical equivalence relations on
    `Raw`, even though their codomains may differ. -/
theorem refines_antisymm_kernel {α β : Type} (L : Lens α) (M : Lens β)
    (h1 : L.refines M) (h2 : M.refines L) :
    ∀ x y, L.equiv x y ↔ M.equiv x y :=
  fun x y => ⟨h1 x y, h2 x y⟩

end E213.Lens.Lattice.Preorder
