# `Lib/Math/Analysis/` — 213-native calculus on Real213

Calculus on top of `Math/Real213` (Cauchy / Series / Differentiation
/ Integration / FluxMVT / ODE / DyadicSearch).  **86 files** total:
7 chapter sub-directories (73 files) + 13 top-level files (6 content
+ 7 umbrella/aggregators).

## Sub-directories (7 chapters)

  - `FluxMVT/`         — flux-form MVT (27 files)
  - `Differentiation/` — differential calculus + polynomial chain (14 files)
  - `DyadicSearch/`    — dyadic-search IVT (13 files; includes G31
                          trajectory-as-witness `MinimalRootLens`)
  - `Integration/`     — definite + indefinite integration (10 files)
  - `ClassicCalc/`     — applied calculus structure (3 files)
  - `ODE/`             — ordinary differential equations (3 files)
  - `Series/`          — power series + convergence (3 files)

## Top-level files (6 content + 7 umbrellas)

  - `BracketCauchyModulus.lean`  — Cauchy-modulus bracket form
  - `CauchyComplete.lean`        — Cauchy completeness witness
  - `CauchyProj.lean`            — Cauchy projection
  - `ChainCauchy.lean`           — Cauchy-chain construction
  - `PhysicsBridgeNT2.lean`      — Physics NT=2 bridge
  - `ResolutionShift.lean`       — resolution-shift lemma
  - `ClassicCalc.lean`, `Differentiation.lean`, `DyadicSearch.lean`,
    `FluxMVT.lean`, `Integration.lean`, `ODE.lean`, `Series.lean`
    — umbrella imports for each sub-directory

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
