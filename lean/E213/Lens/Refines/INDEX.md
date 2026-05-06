# `Hypervisor/Lens/Refines/` — Refines preorder structural facts

Structural theorems about the `Lens.refines` preorder.

## Files (2)

  - `Chain.lean` — Lens chain (`L₁ refines L₂ refines L₃`)
    composition lemmas
  - `Preorder.lean` — preorder properties (refl, trans, antisymm
    failure)

## Public API

Re-exported via `E213.Lens.API` (HV2 — full).

## Where to add new refines theorems

  - Compositional → `Chain.lean`
  - Preorder properties → `Preorder.lean`
