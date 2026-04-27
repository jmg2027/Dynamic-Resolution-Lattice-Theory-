import E213.Hypervisor.Lens

/-!
# Research.RefinesPreorder: Lens.refines 의 preorder 구조

PAPER1 §3.3 의 preorder claim 의 explicit theorems:
reflexivity + transitivity.
-/

namespace E213.Research.RefinesPreorder

open E213.Firmware E213.Hypervisor

/-- Reflexivity. -/
theorem refines_refl {α : Type} (L : Lens α) : L.refines L := by
  intro x y h; exact h

/-- Transitivity. -/
theorem refines_trans {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (h1 : L.refines M) (h2 : M.refines N) : L.refines N := by
  intro x y h; exact h2 x y (h1 x y h)

end E213.Research.RefinesPreorder
