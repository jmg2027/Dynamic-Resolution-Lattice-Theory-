# `Hypervisor/Lens/Compose/` — Lens factoring + composition

How a Lens factors through other Lenses, and how composition
relates to the `refines` preorder.

## Files (7)

  - `Factoring.lean` — `factors_through_implies_refines`:
    if `L = view ∘ M` for some hom, then `L` refines `M`
  - `ImageMinimum.lean` — universal Lens via image
  - `Morphism.lean` — composition as morphism in the Lens category
  - `OnLens.lean` — Lens `α → β` derived from morphism
    [⚠ pre-existing build error: typo `InstancesReach` should
     be `Instances.Reach` (bf34de0); not in API shim until fixed]
  - `OnLensImage.lean` — image construction
  - `OnLensImageGeneric.lean` — generic image (any α)
  - `OnLensImageLevel2.lean` — level-2 image specialisation

## Public API

Re-exported via `E213.Hypervisor.API` (HV5 category, partial —
OnLens excluded due to pre-existing build error).

## Where to add new composition theorems

  - Factoring laws → `Factoring.lean`
  - Image-related → `ImageMinimum.lean`, `OnLensImage*.lean`
