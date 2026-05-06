# `Hypervisor/Lens/Universal/` — Universal Lens construction

Construction of the *universal Lens* — the canonical Lens whose
view is injective (no distinct Raws collapsed).  Gives the
canonical-form equivalence relation on Lenses.

## Files (2)

  - `Flat.lean` — `every_lens_factors_through_idLens`: every Lens
    factors uniquely through the identity Lens.  Direct corollary
    of `Lens.view_unique` (Initiality).
  - `QuotLens.lean` — `universalLens` construction: take the
    quotient of Raw by the kernel of any Lens, you get a Lens
    whose codomain has no quotient distinctions (universal).

## Public API

Re-exported via `E213.Lens.API` (HV6 — Canonical Form API).

## Connection to Meta/

`Meta/UniversalLens/` (11 files) consumes `Universal.QuotLens.
universalLens` to construct concrete universal Lenses at codomains
{ℕ², ℕ³, ℕ⁴, Q213, Q213³} and prove their universality.

## Where to add new universal-construction theorems

  - Generic constructions → `QuotLens.lean`
  - Initiality-derived → `Flat.lean`
