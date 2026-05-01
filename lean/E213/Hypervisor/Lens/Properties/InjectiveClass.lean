import E213.Hypervisor.Lens
import E213.Prelude

/-!
# Research.InjectiveLensClass: the unique equivalence class of injective Lenses

**Observation**: From the perspective of equivalence classes in the
refines preorder, **every injective Lens belongs to the same class**.

## Theorem

If both `L.view` and `M.view` are injective, then `L ≈ M` (they refine each other).

## Significance

Note 37 confirmed that `idLens` is bottom (refines every Lens).
This file adds: **idLens is the injective representative** — every
injective Lens is equivalent to idLens.

That is, the "space" of injective Lenses is a single point (up to equivalence).
-/

namespace E213.Hypervisor.Lens.Properties.InjectiveClass

open E213.Firmware E213.Hypervisor

/-- **Injective equivalence**: two injective Lenses refine each other. -/
theorem injective_equiv {α β : Type} (L : Lens α) (M : Lens β)
    (hL : Function.Injective L.view) (hM : Function.Injective M.view) :
    L.refines M ∧ M.refines L := by
  constructor
  · intro x y hxy
    have heq : x = y := hL hxy
    show M.view x = M.view y
    rw [heq]
  · intro x y hxy
    have heq : x = y := hM hxy
    show L.view x = L.view y
    rw [heq]

end E213.Hypervisor.Lens.Properties.InjectiveClass
