import E213.Hypervisor.Lens.Research.SemanticAtom

/-!
# Research.DistMorphism: Morphisms of the distinguishing-framework category

Structure-preserving morphisms α → β between `HasDistinguishing`
instances.  Identity + composition.

## Design note (sober)

In the trivial Raw instance, `combine x x = x` (idempotent — the
consequence of no same-arg slash).  But general instances (e.g., Nat
with +) are not idempotent (`1 + 1 = 2 ≠ 1`).  Therefore
`universalMorphism α : Raw → α` is not guaranteed to preserve *all*
combine cases — only the diagonal case.

This is a *feature* of the design: the fold structure of `Raw` handles
only distinct args (a direct reflection of axiom 4).  A general morphism
α → β ideally preserves all (x, y), but alignment with Raw is only for
the distinct case.

This file contains only the *abstract* DistMorphism definition
(preservation of all cases) and its identity / composition — the
specific position of Raw is a separate axiom (RawInitiality /
universalMorphism in SemanticAtom).
-/

namespace E213.Hypervisor.Lens.Research.Morphism.Dist

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.SemanticAtom

/-- **Distinguishing-framework morphism** (abstract, all cases). -/
structure DistMorphism (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] where
  toFun : α → β
  preserves_a : toFun d_α.a = d_β.a
  preserves_b : toFun d_α.b = d_β.b
  preserves_combine : ∀ x y, toFun (d_α.combine x y)
                              = d_β.combine (toFun x) (toFun y)

end E213.Hypervisor.Lens.Research.Morphism.Dist

namespace E213.Hypervisor.Lens.Research.Morphism.Dist

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.SemanticAtom

/-- Identity distinguishing morphism. -/
def id (α : Type) [HasDistinguishing α] : DistMorphism α α where
  toFun := fun x => x
  preserves_a := rfl
  preserves_b := rfl
  preserves_combine := fun _ _ => rfl

/-- Composition of distinguishing morphisms. -/
def comp {α β γ : Type} [HasDistinguishing α] [HasDistinguishing β]
    [d_γ : HasDistinguishing γ]
    (f : DistMorphism α β) (g : DistMorphism β γ) : DistMorphism α γ where
  toFun := fun x => g.toFun (f.toFun x)
  preserves_a := by show g.toFun (f.toFun _) = _; rw [f.preserves_a, g.preserves_a]
  preserves_b := by show g.toFun (f.toFun _) = _; rw [f.preserves_b, g.preserves_b]
  preserves_combine := fun x y => by
    show g.toFun (f.toFun (HasDistinguishing.combine x y))
         = d_γ.combine (g.toFun (f.toFun x)) (g.toFun (f.toFun y))
    rw [f.preserves_combine, g.preserves_combine]

/-- Composition is associative. -/
theorem comp_assoc {α β γ δ : Type}
    [HasDistinguishing α] [HasDistinguishing β]
    [HasDistinguishing γ] [HasDistinguishing δ]
    (f : DistMorphism α β) (g : DistMorphism β γ) (h : DistMorphism γ δ) :
    comp (comp f g) h = comp f (comp g h) := rfl

/-- Identity is left-neutral for composition. -/
theorem id_comp {α β : Type} [HasDistinguishing α] [HasDistinguishing β]
    (f : DistMorphism α β) :
    comp (id α) f = f := rfl

/-- Identity is right-neutral for composition. -/
theorem comp_id {α β : Type} [HasDistinguishing α] [HasDistinguishing β]
    (f : DistMorphism α β) :
    comp f (id β) = f := rfl

end E213.Hypervisor.Lens.Research.Morphism.Dist
