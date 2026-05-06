import E213.Hypervisor.Lens.SemanticAtom

/-!
# ImageMinimum: minimum closure of the universalMorphism image

Formal statement that the framework's reach (image of universalMorphism
α) is always the *minimum distinguishing-closed subset* of α.

## Result

```lean
theorem image_minimum_property (α) [d : HasDistinguishing α]
    (S : α → Prop)
    (hSa : S d.a) (hSb : S d.b)
    (hSclosed : ∀ x y, S x → S y → S (d.combine x y)) :
    ∀ r : Raw, S (universalMorphism α r)
```

## Significance

Exact algebraic content of the framework's reach:
- For all S : α → Prop with `d.a, d.b ∈ S` and `S` closed under
  combine, image of universalMorphism ⊆ S.
- That is, the image is the *minimum* distinguishing-closed subset of α.
- → The framework's reach is the strict minimum of
  "distinguishable-closed sub-instances".

## Component of the complete semantic 213 proof

User directive (2026-04-25): do not stop until the complete semantic
proof.  This result is a component of that proof:
- The image of universalMorphism is *uniquely characterized* —
  minimum distinguishing-closed.
- The reach of every semantic framework instance is *uniquely*
  determined framework-internally.
-/

namespace E213.Hypervisor.Lens.Compose.ImageMinimum

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.SemanticAtom

/-- **Image minimum property**: the image of `universalMorphism α` is
    contained in *every* distinguishing-closed subset.  That is, the
    image is the minimum closure. -/
theorem image_minimum_property (α : Type) [d : HasDistinguishing α]
    (S : α → Prop)
    (hSa : S d.a) (hSb : S d.b)
    (hSclosed : ∀ x y, S x → S y → S (d.combine x y))
    (r : Raw) :
    S (universalMorphism α r) := by
  induction r using Raw.rec with
  | a =>
      rw [universalMorphism_a α]
      exact hSa
  | b =>
      rw [universalMorphism_b α]
      exact hSb
  | slash x y h ihx ihy =>
      rw [universalMorphism_slash α x y h]
      exact hSclosed _ _ ihx ihy

end E213.Hypervisor.Lens.Compose.ImageMinimum
