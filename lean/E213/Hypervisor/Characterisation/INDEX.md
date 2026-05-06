# `Hypervisor/Lens/Characterisation/` — Refines-relation catalog

Catalogues which catalog Lenses (HV7 Instances) refine which —
the Hasse-diagram of the `refines` preorder restricted to the
named Lenses in `Instances/`.

## Files (2)

  - `Catalog.lean` — concrete relations (e.g.,
    `parityLens refines leavesLens`, `depthLens incomparable
    leavesLens`)
  - `Core.lean` — abstract characterisation patterns (parametric
    refinement theorems usable across Instances)

## Public API

Imported on demand (HV8 in G12 §4.1 — separate from main API
shim).  Use:
```
import E213.Hypervisor.Characterisation.Catalog
```

## Where to add new characterisation theorems

  - Specific Lens-pair → `Catalog.lean`
  - Parametric pattern → `Core.lean`
