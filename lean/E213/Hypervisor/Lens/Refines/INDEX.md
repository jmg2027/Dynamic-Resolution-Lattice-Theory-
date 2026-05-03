# `Hypervisor/Lens/Refines/` — Refines preorder structural facts

Structural theorems about the `Lens.refines` preorder.

## Files (2)

  - `Chain.lean` — Lens chain (`L₁ refines L₂ refines L₃`)
    composition lemmas.  [⚠ transitively imports
    `Leaves/RefinesParity.lean` which has pre-existing bf34de0
    build errors; not in API shim until fixed]
  - `Preorder.lean` — preorder properties (refl, trans, antisymm
    failure)

## Public API

Re-exported via `E213.Hypervisor.API` (HV2 — partial; Chain
excluded due to transitive dependency on broken file).

## Where to add new refines theorems

  - Compositional → `Chain.lean`
  - Preorder properties → `Preorder.lean`
