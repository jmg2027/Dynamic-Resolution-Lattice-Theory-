import E213.Lens.LensCore

/-!
# RefinesPreorder: preorder structure of Lens.refines

Explicit theorems for the preorder claim in PAPER1 §3.3:
reflexivity + transitivity.
-/

namespace E213.Lens.Refines.Preorder

open E213.Theory E213.Lens

/-- Reflexivity. -/
theorem refines_refl {α : Type} (L : Lens α) : L.refines L := by
  intro x y h; exact h

/-- Transitivity. -/
theorem refines_trans {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (h1 : L.refines M) (h2 : M.refines N) : L.refines N := by
  intro x y h; exact h2 x y (h1 x y h)

end E213.Lens.Refines.Preorder
