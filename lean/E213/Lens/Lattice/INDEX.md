# `Lens/Lattice/` — Lens refines preorder + lattice structure

`Lens.refines` preorder + lattice structure (join / meet).  Folded
2026-05-13 from `Lens/Refines/` (preorder is structurally a Lattice
prerequisite).

## Files (9)

### Refines (preorder)
  - `Chain.lean`    — refines-chain composition (`L₁ ⊑ L₂ ⊑ L₃`)
  - `Preorder.lean` — refl / trans / antisymm-failure of `Lens.refines`

### Lattice (join / meet)
  - `Lattice.lean`    — main lattice scaffolding
  - `Join.lean`       — `joinLens` (LUB) + `joinLens_is_least`
  - `Meet.lean`       — `prodLens` (GLB)
  - `FamilyJoin.lean` — finite-family join (List of Lenses)
  - `FamilyMeet.lean` — finite-family meet
  - `IndexedJoin.lean`— index-set join (∀ i, Lens (α i))
  - `JoinEquiv.lean`  — equivalence properties of join

## Public API

Re-exported via `E213.Lens.API` (HV2 — Refines, HV4 — Lattice).

## Where to add new files

  - Refines-side theorem  → `Chain.lean` / `Preorder.lean`
  - Binary lattice op     → `Join.lean` / `Meet.lean`
  - Family / indexed      → `Family*` / `IndexedJoin`
  - Algebraic identity    → `Lattice.lean`
