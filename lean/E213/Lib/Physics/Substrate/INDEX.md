# `Lib/Physics/Substrate/` — substrate-genesis cluster

The substrate of the DRLT physical model — d=5 unique vertex set,
(NS, NT) = (3, 2) bipartition, 10 pairs, c=2 doubling.  Cluster
holds the explicit 26-conjunct synthesis + Phase-1 bridge +
falsifier.

## Files (13)

### Forced derivations
  - `Origin.lean`        — d = 5 unique (forced by Atomicity)
  - `Shape.lean`         — 5 vertices, (NS, NT) = (3, 2), 10 pairs
  - `Existence.lean`     — `Vertex := Fin 5` + block classification

### Combinatorial structure
  - `Pairs.lean`         — AA(3) + BB(1) + AB(6) = 10
  - `Edges.lean`         — c = 2 doubling, b₁ = 8 = NS² − 1
  - `Time.lean`          — NT = 2 → 2ⁿ dyadic
  - `Space.lean`         — NS = 3 → 3ⁿ ternary, NS/NT asymmetry

### Observables + interactions
  - `Observable.lean`    — 9 framework-level measurable integers
  - `Force.lean`         — 3 channels = 3 force candidates
  - `Lens.lean`          — explicit Lens (parityLens) on substrate

### Capstone + bridge + falsifier
  - `Capstone.lean`      — 26-conjunct single synthesis
  - `Phase1Bridge.lean`  — substrate ↔ Phase-1 arithmetic identity
  - `Falsifier.lean`     — CLAUDE.md criterion (2) falsifiable props

## Top-level

  - `Substrate.lean` aggregator

## Axiom status

All 0 sorry.  Most files completely axiom-free (rfl + decide);
remaining stay within Lean 4 core (≤ propext + Quot.sound).

## Operating principles (CLAUDE.md)

Avoid "observer / structure / relation / space / perception" in
framework-level descriptions.  Only "primitive distinction"; every
other notion is explicit Lens output.

## Where to add new files

  - Forced derivation     → `Origin*` / `Shape*` / `Existence*`
  - Combinatorial counts  → `Pairs` / `Edges` / `Time` / `Space`
  - Observable / force    → `Observable` / `Force`
  - Capstone synthesis    → `Capstone` (consolidate, don't split)
  - Falsifier proposition → `Falsifier`
