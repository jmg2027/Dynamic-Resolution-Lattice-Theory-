# `Hypervisor/Lens/Compose/` — Lens factoring + composition

How a Lens factors through other Lenses, and how composition
relates to the `refines` preorder.

## Files (7)

  - `Factoring.lean` — `factors_through_implies_refines`:
    if `L = view ∘ M` for some hom, then `L` refines `M`
  - `ImageMinimum.lean` — universal Lens via image
  - `Morphism.lean` — composition as morphism in the Lens category
  - `OnLens.lean` — Lens `α → β` derived from morphism
  - `OnLensImage.lean` — image construction
  - `OnLensImageGeneric.lean` — generic image (any α)
  - `OnLensImageLevel2.lean` — level-2 image specialisation

## Public API

Re-exported via `E213.Lens.API` (HV5 category — full).

## Where to add new composition theorems

  - Factoring laws → `Factoring.lean`
  - Image-related → `ImageMinimum.lean`, `OnLensImage*.lean`
