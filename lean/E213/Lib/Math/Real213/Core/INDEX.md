# `Real213/Core/` — Real213 type + core operations

The base 213-native real-number type (Dedekind cut representation),
core algebraic structure, validity predicate, and equiv/poset.

## Files (11)

### Type + carrier
  - `Core.lean`              — `RealCut` core type
  - `CutFnData.lean`         — function-data wrapper
  - `Dyadic.lean`            — dyadic cut subtype
  - `ValidCut.lean`          — validity predicate
  - `ValidCutOps.lean`       — operations preserving validity

### Equiv / poset
  - `Equiv.lean`             — Cut-level equivalence
  - `CutPoset.lean`           — poset structure
  - `MinimumProposition.lean` — minimum-element witness

### Algebra structure
  - `CutAlgebraStruct.lean`  — algebra-structure scaffolding
  - `Functions.lean`         — function-on-cut combinators
  - `AsLensOutput.lean`      — RealCut as a Lens output

## Where to add new files

  - New cut representation lemma → `Cut<...>` / `Valid<...>`
  - Poset/equiv extension        → `Equiv` / `CutPoset`
  - Algebra structure            → `CutAlgebraStruct`
  - Lens-output wiring           → `AsLensOutput`
