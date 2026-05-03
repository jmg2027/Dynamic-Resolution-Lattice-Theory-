/-!
# `Funext.lean` — funext as the "pointwise-equal functions collapse" lens

★ G12 Tier 4 A2 — funext reformulated as a 213-internal lens.

`funext : (∀ x, f x = g x) → f = g` is provable in Lean 4 from
`Quot.sound`.  Reading 213-internally:
  - The Raw substrate distinguishes functions that have the same
    pointwise values but different intensional structure.
  - `funext` is a LENS choice: collapse pointwise-equal functions
    into the same equivalence class.
  - Without `funext`: each function is its own thing; pointwise
    equality is a relation, not identity.
  - With `funext`: function-types become quotients by pointwise eq.

This is the lens we explicitly DIDN'T apply in the funext-refactor.
The `_at` variants (Real213/, Cohomology/) live in the no-funext
view — strict ∅-axiom.  The function-eq wrappers live in the
funext-applied view — DIRTY [Quot.sound].

The 4 lens objects in `Hypervisor/Lens/Instances/{Pointwise
Projection, EndpointBehavior, BoundedContext, CochainEntry}.lean`
formalise the no-funext views explicitly.
-/

namespace E213.Hypervisor.Lens.AxiomLenses.Funext

/-- The funext-lens equivalence: two functions agree iff they
    have the same value at every input. -/
def pointwiseEq {α β : Type} (f g : α → β) : Prop :=
  ∀ x, f x = g x

theorem pointwiseEq_refl {α β : Type} (f : α → β) : pointwiseEq f f :=
  fun _ => rfl

theorem pointwiseEq_symm {α β : Type} {f g : α → β}
    (h : pointwiseEq f g) : pointwiseEq g f :=
  fun x => (h x).symm

theorem pointwiseEq_trans {α β : Type} {f g h : α → β}
    (hfg : pointwiseEq f g) (hgh : pointwiseEq g h) : pointwiseEq f h :=
  fun x => (hfg x).trans (hgh x)

/-- The trivial direction (Eq → pointwise eq) is constructive. -/
theorem eq_implies_pointwiseEq {α β : Type} {f g : α → β} (h : f = g) :
    pointwiseEq f g := fun x => h ▸ rfl

/-- The non-trivial direction (pointwise eq → Eq) IS funext.
    We can state it as a lens application — the lens is "apply
    funext" and its codomain is `f = g`. -/
abbrev funextLens {α β : Type} (f g : α → β) : Prop :=
  pointwiseEq f g → f = g

/-- Lean 4 provides this lens for every (α, β, f, g) via Quot.sound.
    The 213-strict-∅-axiom standard says: "we don't apply this lens
    by default; use it only at explicit boundaries."  Hence our
    `_at` variants survive ∅-axiom while function-eq wrappers
    inherit Quot.sound from this lens. -/
theorem funextLens_inhabited {α β : Type} (f g : α → β) :
    funextLens f g := funext

end E213.Hypervisor.Lens.AxiomLenses.Funext
