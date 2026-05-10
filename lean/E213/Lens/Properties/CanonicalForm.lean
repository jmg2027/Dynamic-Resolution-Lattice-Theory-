import E213.Lens.Universal.QuotLens
import E213.Lens.Algebra.Congruence

/-!
# LensCanonicalForm: canonical form of a Lens via universalLens

Explicit refines-equivalence wrapping of `universalLens_recovers`
(UniversalQuotLens.lean).  Formal expression of the framework's
*self-stabilization*:

> Any Lens `M` is refines-equivalent to `universalLens M.equiv`.
>
> The framework reconstructs any of its own Lenses from its own
> kernel *up to refines-equivalence*.

## Significance

- `universalLens` is the canonical form of every Lens.
- The refines-equivalence class of a Lens is parameterized by a
  slash-congruence.
- The framework is closed within itself: the Lens space reconstructs
  from its own quotient.

Analysis of Note 78.
-/

namespace E213.Lens.Properties.CanonicalForm

open E213.Theory E213.Lens
open E213.Lens.Universal.QuotLens

/-- **Lens refines-equivalence**: two Lenses share the same kernel. -/
def refinesEquiv {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  L.refines M ∧ M.refines L

theorem refinesEquiv_refl {α} (L : Lens α) : refinesEquiv L L :=
  ⟨Lens.refines_refl L, Lens.refines_refl L⟩

theorem refinesEquiv_symm {α β} {L : Lens α} {M : Lens β} :
    refinesEquiv L M → refinesEquiv M L
  | ⟨h1, h2⟩ => ⟨h2, h1⟩

end E213.Lens.Properties.CanonicalForm

namespace E213.Lens.Properties.CanonicalForm

open E213.Theory E213.Lens
open E213.Lens.Universal.QuotLens

/-- **Self-stabilization**: any Lens M is refines-equivalent to
    `universalLens M.equiv`. -/
theorem lens_canonical_universal {α : Type} (M : Lens α)
    (hsym : ∀ u v, M.combine u v = M.combine v u) :
    refinesEquiv M (universalLens M.equiv) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    show (universalLens M.equiv).view x = (universalLens M.equiv).view y
    exact (universalLens_recovers α M hsym x y).mpr hxy
  · intro x y hxy
    show M.view x = M.view y
    exact (universalLens_recovers α M hsym x y).mp hxy

/-- **Idempotent canonical form**: universalLens is a fixed-point. -/
theorem lens_canonical_idempotent {α : Type} (M : Lens α) :
    refinesEquiv (universalLens M.equiv)
                 (universalLens (universalLens M.equiv).equiv) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    show (universalLens (universalLens M.equiv).equiv).view x
         = (universalLens (universalLens M.equiv).equiv).view y
    exact (universalLens_idempotent α M x y).mpr hxy
  · intro x y hxy
    show (universalLens M.equiv).view x = (universalLens M.equiv).view y
    exact (universalLens_idempotent α M x y).mp hxy

end E213.Lens.Properties.CanonicalForm
