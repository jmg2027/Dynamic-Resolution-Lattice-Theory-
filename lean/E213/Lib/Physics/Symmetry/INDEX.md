# `Lib/Physics/Symmetry/` — automorphism + orbit symmetry

K_{3,2}^{(c=2)} automorphism group, edge action, orbits, chiral
structure, gluon-channel interpretation.

## Files (6)

  - `AutAction.lean`                 — automorphism action on Raw / lattice
  - `AutEdgeAction.lean`             — auto action on edges
  - `AutEdgeActionGenerators.lean`   — generators of the edge action
  - `AutEdgeOrbits.lean`             — edge orbit classification
  - `AutKChiral.lean`                — chiral auto-action on K
  - `GluonChannelInterpretation.lean` — gluon-channel physics reading

## Top-level

  - `Symmetry.lean` aggregator

## Where to add new files

  - Auto-action / orbits      → `Aut<...>` family
  - Generator catalog         → `AutEdgeAction<...>Generators`
  - Physics interpretation    → `<Channel>Interpretation.lean`
