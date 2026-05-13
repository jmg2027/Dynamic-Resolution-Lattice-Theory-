import E213.Lens.LensCore
import E213.Prelude
import E213.Lens.Instances.Identity
import E213.Lens.Lattice.Lattice

/-!
# Meta.UniversalLens — Universal Lens metatheory

User-articulated thesis: 213 is not described from outside;
it is the precondition for any "describing".  A Universal Lens
is the lens built into the act of referring.  Formal core:

  L is universal iff `L.view : Raw → α` is injective.

Collapses three constraints:
  (1) catamorphism — given by `Lens.view = Raw.fold ...`
  (2) Axiom-2 preservation — `view` injective ⇔ no aliasing
  (3) self-anchoring — `L.view O` serves as origin in α

Heavy lifting reused from `Research.IdentityLens` (existence:
`idLens` itself) and `Research.LensLattice` (refinement lattice).
-/

namespace E213.Lens.Universal.Witnesses.Core

open E213.Theory E213.Lens
open E213.Lens.Instances.Identity (idLens idLens_injective)
open E213.Lens.Lattice.Lattice (refines_idLens_iff_injective)

/-- A Lens is *universal* iff its view is injective on Raw. -/
def IsUniversal {α : Type} (L : Lens α) : Prop :=
  Function.Injective L.view

/-- Origin at observer O: the basepoint of α relative to O. -/
def OriginAt {α : Type} (L : Lens α) (O : Raw) : α := L.view O

/-- A universal lens distinguishes the observer from any distinct Raw. -/
theorem distinguishes {α : Type} (L : Lens α)
    (h : IsUniversal L) {O X : Raw} (hne : O ≠ X) :
    L.view O ≠ L.view X := fun heq => hne (h heq)

/-- Universality ↔ refining the identity lens. -/
theorem universal_iff_refines_idLens {α : Type} (L : Lens α) :
    IsUniversal L ↔ L.refines idLens :=
  (refines_idLens_iff_injective L).symm

/-- The identity lens is universal (existence witness). -/
theorem idLens_is_universal : IsUniversal idLens := idLens_injective

/-- ★★★ Existence: a Universal Lens exists. -/
theorem universal_exists : ∃ (α : Type) (L : Lens α), IsUniversal L :=
  ⟨Raw, idLens, idLens_is_universal⟩

/-- A universal lens refines every other lens (finest-lens property). -/
theorem refines_all {α β : Type} (L : Lens α) (M : Lens β)
    (h : IsUniversal L) : L.refines M := by
  intro x y hxy
  have hxy_eq : x = y := h hxy
  show M.view x = M.view y
  rw [hxy_eq]

/-- ★★★★★ Universal Lens capstone — formal core of the
    "213 as precondition" thesis. -/
theorem universal_lens_capstone :
    (∃ (α : Type) (L : Lens α), IsUniversal L)
    ∧ (∀ {α β : Type} (L : Lens α) (M : Lens β),
         IsUniversal L → L.refines M) :=
  ⟨universal_exists, fun L M h => refines_all L M h⟩

end E213.Lens.Universal.Witnesses.Core
