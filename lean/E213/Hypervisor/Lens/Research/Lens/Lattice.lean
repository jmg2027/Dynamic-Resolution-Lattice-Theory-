import E213.Hypervisor.Lens.Research.Lens.Identity

/-!
# Research.LensLattice: structure of Lens.refines

`Lens.refines` (Hypervisor/Lens.lean) is a preorder on the kernels
of Lenses.  `L.refines M` iff `L.equiv` is finer than `M.equiv`
(L.ker ⊆ M.ker).

This file makes explicit the two ends of the preorder:

- **Bottom (finest kernel)**: `idLens` — equiv = `=` (Raw equality).
  Refines every Lens.
- **Top (coarsest kernel)**: `constLens e` — equiv = Raw × Raw
  (everything equal).  Refined by every Lens.

**Therefore**: L.view is injective ↔ L refines idLens (L.ker ⊆ `=`).

## Significance

Whereas the diagonal analysis of Notes 34-36 concerned the data of
individual Lenses, this file treats the **relationships between**
Lenses.  The refines preorder provides the structure of the Lens
world.
-/

namespace E213.Hypervisor.Lens.Research.Lens.Lattice

open E213.Firmware E213.Hypervisor E213.Hypervisor.Lens.Research.Lens.Identity

/-- Terminal Lens: maps every Raw to a single point e. -/
def constLens {α : Type} (e : α) : Lens α where
  base_a := e
  base_b := e
  combine _ _ := e

theorem constLens_view {α : Type} (e : α) (r : Raw) :
    (constLens e).view r = e := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : (constLens e).view (Raw.slash x y h)
                   = (constLens e).combine
                       ((constLens e).view x) ((constLens e).view y) :=
        Raw.fold_slash _ _ _ (by intro _ _; rfl) x y h
      rw [hfs]; rfl

end E213.Hypervisor.Lens.Research.Lens.Lattice

namespace E213.Hypervisor.Lens.Research.Lens.Lattice

open E213.Firmware E213.Hypervisor E213.Hypervisor.Lens.Research.Lens.Identity

/-- **Bottom**: idLens refines every Lens.  Since the kernel of
    idLens is Raw equality `=`, it is contained in every kernel. -/
theorem idLens_refines_all {α : Type} (L : Lens α) :
    idLens.refines L := by
  intro x y hxy
  have h : idLens.view x = idLens.view y := hxy
  rw [idLens_is_id, idLens_is_id] at h
  show L.view x = L.view y
  rw [h]

/-- **Top**: every Lens refines constLens e.  The kernel of constLens
    is universal (everything is equal). -/
theorem all_refine_constLens {α : Type} (e : α) (L : Lens α) :
    L.refines (constLens e) := by
  intro x y _
  show (constLens e).view x = (constLens e).view y
  rw [constLens_view, constLens_view]

end E213.Hypervisor.Lens.Research.Lens.Lattice

namespace E213.Hypervisor.Lens.Research.Lens.Lattice

open E213.Firmware E213.Hypervisor E213.Hypervisor.Lens.Research.Lens.Identity

/-- **Injectivity characterisation**: L refines idLens ↔ L.view is
    injective. -/
theorem refines_idLens_iff_injective {α : Type} (L : Lens α) :
    L.refines idLens ↔ Function.Injective L.view := by
  constructor
  · intro h x y hxy
    have hk : idLens.view x = idLens.view y := h x y hxy
    rw [idLens_is_id, idLens_is_id] at hk
    exact hk
  · intro hinj x y hxy
    have heq : x = y := hinj hxy
    show idLens.view x = idLens.view y
    rw [heq]

/-- If constLens e refines some L, then L is also constant. -/
theorem constLens_refines_iff_const {α β : Type} (e : α) (L : Lens β) :
    (constLens e).refines L ↔ ∀ x y : Raw, L.view x = L.view y := by
  constructor
  · intro h x y
    apply h x y
    show (constLens e).view x = (constLens e).view y
    rw [constLens_view, constLens_view]
  · intro hconst x y _
    exact hconst x y

end E213.Hypervisor.Lens.Research.Lens.Lattice
