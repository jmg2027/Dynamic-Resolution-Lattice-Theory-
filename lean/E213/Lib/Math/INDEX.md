# `Lib/Math/` — 213-native mathematics library

213-native mathematics (~38 sub-cluster umbrellas).  Importing
`Math.lean` pulls in every Math sub-tree.

## Top-level umbrellas

### Core analysis foundation
  - `Real213.lean`         — 213-native real-number type (cuts)
  - `Analysis.lean`        — calculus (7 chapter sub-dirs)
  - `Cauchy.lean`          — Cauchy/Euler/Wallis/Pell sequences
  - `Modulus.lean`         — modulus combinators
  - `CascadeCalculus.lean` — cascaded-calculus structure
  - `Multivariable.lean`   — multivariable analysis
  - `ODE.lean`             — ODE
  - `Measure.lean`         — measure theory
  - `Functional.lean`      — functional analysis

### Algebra + number theory
  - `CayleyDickson.lean`   — CD layered construction (5 sub-dirs)
  - `ModArith.lean`        — modular arithmetic / Bezout / CRT
  - `Linalg213.lean`       — 213-native linear algebra
  - `Polynomial213.lean`   — coefficient-array polynomials
  - `Hyper.lean`           — hypernumbers
  - `Padic.lean`           — p-adic ℤ_p[√D] cluster (Hensel, Frobenius)
  - `Group.lean`           — group structure
  - `SignedCut.lean`       — signed-cut algebra (6 sub-dirs)
  - `Slots.lean`           — the slot programme (signed normal form, 4-axis Gauss tuple, pair exponents, collapse-vs-rigid)
  - `Complex.lean`         — complex on Real213
  - `Irrational.lean`      — irrationality without ZFC
  - `IntSqrt.lean`         — integer square root
  - `Icosahedral.lean`     — icosahedral / H₃ structure
  - `Mobius213.lean`,
    `Mobius213OneAsGlue.lean`,
    `Mobius213GrandUnification.lean`,
    `Mobius213SignatureAxisCatalogPhase2.lean` — Möbius matrix [[2,1],[1,1]] + signature-axis catalogue

### Topology + structure
  - `Topology.lean`        — base topology
  - `LevelTopology.lean`   — level-tower topology (6 files)
  - `Combinatorics.lean`   — combinatorics
  - `Pigeonhole.lean`      — pigeonhole infrastructure
  - `AngleStructure.lean`  — angle structure
  - `TriangularTower.lean` — triangular tower
  - `AkbulutCork.lean`     — Akbulut cork (exotic 4-manifold seed)

### Cohomology + Hodge
  - `Cohomology.lean`      — base cohomology (11 sub-dirs)
  - `HodgeConjecture.lean` — Hodge programme (7 sub-dirs)

### Foundations + meta
  - `AxiomSystems.lean`    — Peano / ZFC / classical-analysis-as-Lens
  - `Choice.lean`          — choice (no Classical.choice)
  - `ResolutionLimit.lean` — resolution-limit witness
  - `Logic.lean`           — logic primitives
  - `Search.lean`          — search algorithms

### Specialized
  - `DyadicFSM.lean`           — dyadic FSM (12 sub-dirs)
  - `Probability.lean`         — probability (5 sub-dirs)
  - `Information.lean`         — information theory
  - `PatternCatalog.lean`      — 213 pattern catalog
  - `Tactic.lean`              — math-side tactics
  - `Extras.lean`              — auxiliary results

### Cross-domain
  - `ParadigmDomain.lean`,
    `ParadigmDomainGraded.lean`,
    `ParadigmDomainGradedRing.lean`,
    `ParadigmDomainPhysics.lean` — graded ring on the paradigm + physics face
  - `GradedRingConfigCountBridge.lean` — graded ring ↔ configCount bridge
  - `CrossDomainUnification.lean`    — domain unification capstone
  - `PrimeDescentObservations.lean`  — prime-descent observations

## Sub-directories (~38)

Each top-level `.lean` is the aggregator for the matching directory.
Per-cluster `INDEX.md` (where present) details the file catalog.

## Where to add new files

  - New mathematical topic     → new directory + aggregator + INDEX
  - Single result in cluster   → matching cluster directory
  - Cross-cluster bridge       → `<Topic>Bridge.lean` (anti-corruption
                                  layer pattern)

## Companion rings

  - `Lib/Physics/`  — physics deployment (consumes Math)
  - `Theory/`       — Raw axiom + Atomicity (consumed by Math)
  - `Lens/`         — Lens framework (consumed by Math)
  - `Meta/`         — ring-independent helpers
