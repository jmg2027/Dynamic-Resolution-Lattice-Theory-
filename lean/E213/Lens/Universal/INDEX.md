# `Lens/Universal/` — Universal Lens construction + witnesses

Construction of the *universal Lens* — the canonical Lens whose
view is injective (no distinct Raws collapsed).  Gives the
canonical-form equivalence relation on Lenses.

## Files (Tier 1 — Construction, 2)

  - `Flat.lean` — `every_lens_factors_through_idLens`: every Lens
    factors uniquely through the identity Lens.  Direct corollary
    of `Lens.view_unique` (Initiality).
  - `QuotLens.lean` — `universalLens` construction: take the
    quotient of Raw by the kernel of any Lens, you get a Lens
    whose codomain has no quotient distinctions (universal).

## Witnesses (sub-cluster — concrete instances, 11)

Concrete universal-Lens instances at canonical codomains.

  - `Witnesses/Core.lean`              — universal-Lens carrier
  - `Witnesses/Nat2.lean`              — Nat-arity-2 codomain
  - `Witnesses/Nat2Inj.lean`           — Nat2 injectivity proof
  - `Witnesses/Nat3.lean`              — Nat-arity-3 codomain
  - `Witnesses/Nat4.lean`              — Nat-arity-4 codomain
  - `Witnesses/Q213.lean`              — Q213 rational codomain
  - `Witnesses/Q213Inj.lean`           — Q213 injectivity proof
  - `Witnesses/Q213_3.lean`            — Q213³ codomain
  - `Witnesses/Padding.lean`           — padding theorems
  - `Witnesses/PaddingCapstone.lean`   — padding capstone
  - `Witnesses/TripleCapstone.lean`    — triple-capstone integration

Witnesses moved 2026-05-13 from `Meta/UniversalLens/` per LENS_AUDIT
§4 — these are concrete Lens instances (Lens-content) rather than
ring-independent Meta primitives.  Namespace renamed
`E213.Meta.UniversalLens.*` → `E213.Lens.Universal.Witnesses.*`.

## Public API

Re-exported via `E213.Lens.API` (HV6 — Canonical Form API).
Witnesses are also re-exported via `Lens.Universal.lean` umbrella.

## Where to add new universal-construction theorems

  - Generic constructions       → `QuotLens.lean`
  - Initiality-derived          → `Flat.lean`
  - Concrete codomain witnesses → `Witnesses/`
