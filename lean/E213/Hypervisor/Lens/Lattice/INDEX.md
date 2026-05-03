# `Hypervisor/Lens/Lattice/` — Lens lattice structure

The `refines` preorder on `Lens α` carries a lattice structure.
This sub-cluster provides join (least upper bound) and meet
(greatest lower bound) constructions, plus their universal
properties.

## Files (7)

  - `Lattice.lean` — main lattice scaffolding
  - `Join.lean` — `joinLens` (binary least upper bound) +
    universal property `joinLens_is_least`
  - `Meet.lean` — `prodLens` (binary greatest lower bound)
  - `FamilyJoin.lean` — finite-family join (List of Lenses)
  - `FamilyMeet.lean` — finite-family meet
  - `IndexedJoin.lean` — index-set join (∀ i, Lens (α i))
  - `JoinEquiv.lean` — equivalence properties of join

## Public API

Re-exported via `E213.Hypervisor.API` (HV4 category).

## Where to add new Lens-lattice theorems

  - Binary operations → `Join.lean` or `Meet.lean`
  - Family/indexed → `FamilyJoin.lean`, `FamilyMeet.lean`,
    `IndexedJoin.lean`
  - Algebraic identities → `Lattice.lean`
