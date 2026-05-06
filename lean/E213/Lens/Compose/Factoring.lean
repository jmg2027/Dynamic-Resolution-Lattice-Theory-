import E213.LensCore

/-!
# LensFactoring: general sufficient condition for refines

**Claim**: if M.view factors through L.view, then L.refines M.

```
M.view = g ∘ L.view for some g : α → β  ⟹  L.refines M
```

This formalizes "M uses only the information provided by L."
It is the **unified tool** for all catalogue refines relationships
(note 38 §7 Q37.2).

The converse direction is non-constructive (requires AC).  This file
provides only the constructive direction.
-/

namespace E213.Lens.Compose.Factoring

open E213.Theory E213.Lens

/-- **Factoring → Refinement**: if M.view factors through L.view,
    then L.refines M. -/
theorem refines_of_factor {α β : Type} (L : Lens α) (M : Lens β)
    (g : α → β) (hfactor : ∀ r : Raw, M.view r = g (L.view r)) :
    L.refines M := by
  intro x y hxy
  have hxy' : L.view x = L.view y := hxy
  show M.view x = M.view y
  rw [hfactor x, hfactor y, hxy']

end E213.Lens.Compose.Factoring
