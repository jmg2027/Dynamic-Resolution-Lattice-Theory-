import E213.Hypervisor.Lens

/-!
# Research.LensEquivProperties: Lens.equiv 가 equivalence relation

PAPER1 §3.2 의 `Lens.equiv` 가 reflexivity + symmetry +
transitivity 만족 의 explicit theorems.
-/

namespace E213.Research.LensEquivProperties

open E213.Firmware E213.Hypervisor

theorem lens_equiv_refl {α : Type} (L : Lens α) (x : Raw) :
    L.equiv x x := rfl

theorem lens_equiv_symm {α : Type} (L : Lens α) (x y : Raw) :
    L.equiv x y → L.equiv y x := by
  intro h; exact h.symm

theorem lens_equiv_trans {α : Type} (L : Lens α) (x y z : Raw) :
    L.equiv x y → L.equiv y z → L.equiv x z := by
  intros h1 h2; exact h1.trans h2

end E213.Research.LensEquivProperties
