# `Lib/Math/Analysis/` — 213-native calculus on Real213

Calculus on top of `Math/Real213` (Cauchy / Series / Differentiation
/ Integration / FluxMVT / ODE / DyadicSearch).  Cluster organises 7
chapter sub-directories + 6 top-level Cauchy / bridge files.

## Sub-directories (7 chapters)

  - `ClassicCalc/`     — applied calculus structure (3 files)
  - `Differentiation/` — differential calculus + polynomial chain
                          (14 files, see INDEX)
  - `DyadicSearch/`    — dyadic-search IVT (9 files; includes G31
                          trajectory-as-witness `MinimalRootLens`)
  - `FluxMVT/`         — flux-form MVT (22 files, see INDEX)
  - `Integration/`     — definite + indefinite integration
                          (10 files, see INDEX)
  - `ODE/`             — ordinary differential equations
  - `Series/`          — power series + convergence

## Top-level files (6, all Cauchy / bridge)

  - `BracketCauchyModulus.lean`  — Cauchy-modulus bracket form
  - `CauchyComplete.lean`        — Cauchy completeness witness
  - `CauchyProj.lean`            — Cauchy projection
  - `ChainCauchy.lean`           — Cauchy-chain construction
  - `PhysicsBridgeNT2.lean`      — Physics NT=2 bridge
  - `ResolutionShift.lean`       — resolution-shift lemma

## Aggregator

  - `Analysis.lean` — imports all sub-directories + top-level files

## Where to add new files

  - Cauchy / bracket / projection → top-level `Cauchy*` / `Bracket*`
  - Differential calculus         → `Differentiation/`
  - Integration                   → `Integration/`
  - Search / IVT                  → `DyadicSearch/`
  - Flux / MVT                    → `FluxMVT/`
  - Series                        → `Series/`
  - ODE                           → `ODE/`
  - Classic-applied                → `ClassicCalc/`

## Companion clusters

  - `Math/Real213/` — base real type (cuts + algebra)
  - `Math/Cauchy/`  — Cauchy / Euler / Wallis / Pell sequences
  - `Math/Modulus/` — modulus combinators
