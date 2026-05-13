# `DyadicFSM/Product/` — product FSM constructions

Product of two dyadic FSMs: `ProductFSM`, period analysis, run
combinators, LCM closure, cross-class Lens.

## Files (7)

### Core construction
  - `ProductFSM.lean`            — `ProductFSM` base type
  - `ProductFSMRun.lean`         — run combinator
  - `ProductHelpers.lean`        — helper lemmas

### Period analysis
  - `ProductFSMPeriod.lean`      — period computation
  - `ProductFSMPeriodDvd.lean`   — period divisibility

### Closure + Lens
  - `LCMClosure.lean`            — LCM-closure under product
  - `CrossClassLens.lean`        — cross-class Lens witness

## Where to add new files

  - Product construction      → `ProductFSM<...>` /
                                 `Product<combinator>.lean`
  - Period theorem            → `ProductFSMPeriod<...>`
  - Closure / Lens            → `<X>Closure.lean` / `<X>Lens.lean`

## Companion clusters

  - `DyadicFSM/ArithFSM/`     — Tier 1 multi-state FSM
  - `DyadicFSM/BitFSM`        — base BitFSM
  - `DyadicFSM/Fib/`          — Fibonacci product witness
