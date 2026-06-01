import E213.Lens.Universal.QuotLens
import E213.Lens.Algebra.Congruence

/-!
# LensCanonicalForm: canonical form of a Lens via universalLens

Explicit refines-equivalence wrapping of `universalLens_recovers_R`
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

/-- **Lens refines-equivalence**: two Lenses share the same kernel.  Stated on
    the codomain-polymorphic `refinesG`, so each side reads its own codomain's
    sameness (`equivR` at `Raw → Prop`, `equiv` at the default instance) — the
    refines-equivalence is ∅-axiom even when one side is the `Raw → Prop`
    canonical form. -/
def refinesEquiv {α β : Type} [ReadingEq α] [ReadingEq β] (L : Lens α) (M : Lens β) :
    Prop :=
  L.refinesG M ∧ M.refinesG L

theorem refinesEquiv_refl {α} [ReadingEq α] (L : Lens α) : refinesEquiv L L :=
  ⟨Lens.refinesG_refl L, Lens.refinesG_refl L⟩

theorem refinesEquiv_symm {α β} [ReadingEq α] [ReadingEq β]
    {L : Lens α} {M : Lens β} :
    refinesEquiv L M → refinesEquiv M L
  | ⟨h1, h2⟩ => ⟨h2, h1⟩


/-- **Self-stabilization**: any Lens M is refines-equivalent to
    `universalLens M.equiv`.  ∅-axiom, via `universalLens_recovers_R`. -/
theorem lens_canonical_universal {α : Type} (M : Lens α)
    (hsym : ∀ u v, M.combine u v = M.combine v u) :
    refinesEquiv M (universalLens M.equiv) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    exact (universalLens_recovers_R α M hsym x y).mpr hxy
  · intro x y hxy
    exact (universalLens_recovers_R α M hsym x y).mp hxy

/-- **Idempotent canonical form**: universalLens is a fixed-point.  Stated on the
    Reading-native kernel (`equivR`), ∅-axiom via `universalLens_idempotent_R`. -/
theorem lens_canonical_idempotent {α : Type} (M : Lens α) :
    refinesEquiv (universalLens M.equiv)
                 (universalLens ((universalLens M.equiv).equivR)) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    exact (universalLens_idempotent_R M.equiv x y).mpr hxy
  · intro x y hxy
    exact (universalLens_idempotent_R M.equiv x y).mp hxy

end E213.Lens.Properties.CanonicalForm
