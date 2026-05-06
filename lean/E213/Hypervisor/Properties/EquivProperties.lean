import E213.HypervisorCore

/-!
# LensEquivProperties: Lens.equiv is an equivalence relation

Explicit theorems that `Lens.equiv` satisfies reflexivity + symmetry +
transitivity, as stated in PAPER1 §3.2.
-/

namespace E213.Hypervisor.Properties.EquivProperties

open E213.Firmware E213.Hypervisor

theorem lens_equiv_refl {α : Type} (L : Lens α) (x : Raw) :
    L.equiv x x := rfl

theorem lens_equiv_symm {α : Type} (L : Lens α) (x y : Raw) :
    L.equiv x y → L.equiv y x := by
  intro h; exact h.symm

theorem lens_equiv_trans {α : Type} (L : Lens α) (x y z : Raw) :
    L.equiv x y → L.equiv y z → L.equiv x z := by
  intros h1 h2; exact h1.trans h2

end E213.Hypervisor.Properties.EquivProperties
