# `Lib/Math/Analysis/FluxMVT/` — flux-form Mean Value Theorem

213-native cohomological reformulation of the Mean Value Theorem.
Tracks *flux through endpoints* instead of tangent slopes — works
in the 213 substrate (no exact derivatives, only bracketed cuts).

## Files (27)

### Flux core (5)
  - `FluxCut.lean`        — flux as a cut-level value
  - `FluxCochain.lean`    — flux as a Cochain (cohomological)
  - `FluxDivergence.lean` — divergence theorem at cut level
  - `FluxEquiv.lean`      — flux-equivalence relation
  - `FluxEquivOps.lean`   — ops compatible with flux-equiv

### MVT witnesses (7)
  - `FluxMVT.lean`                     — generic flux-MVT
  - `FluxMVTConcrete.lean`             — concrete witness
  - `FluxMVTWitness.lean`              — witness builder
  - `FluxMVTWitnessCombinators.lean`   — combinators
  - `MVTWitnessCatalog.lean`           — catalogue
  - `MVTWitnessChain.lean`             — chain composition
  - `DyadicMVTWitness.lean`            — dyadic-bracket variant

### Polynomial / passthrough (7)
  - `FluxPolynomial.lean`              — polynomial-flux base
  - `FluxMVTPolynomial.lean`           — MVT on polynomial input
  - `FluxFTCPolynomial.lean`           — FTC on polynomial input
  - `FluxMVTPassthrough.lean`          — passthrough construction
  - `FluxPassthroughCatalog.lean`      — passthrough catalogue
  - `FluxPassthroughClass.lean`        — passthrough class
  - `FluxMVTPropagate.lean`            — propagation lemmas

### FTC + series (3)
  - `FluxFTC.lean`        — fundamental-theorem-of-calculus, flux form
  - `FTCRiemann.lean`     — Riemann-form FTC
  - `FluxSeries.lean`     — flux applied to series

### Bracket + telescope machinery (4)
  - `AdjacentSternBrocotBridge.lean` — adjacent Stern-Brocot bridge
  - `TelescopingConservation.lean`   — telescoping conservation law
  - `UnitBracketReduce.lean`         — unit-bracket reduction
  - `UnitBracketReduceSum.lean`      — unit-bracket reduction (sum form)

## Top-level

  - `FluxMVT.lean` (aggregator) — see for full per-section docstring
  - `QuintupleTelescope.lean` — quintuple MVT chain at d-depth 5

## Where to add new files

  - New MVT shape          → `FluxMVTWitness*` style
  - Polynomial extension   → `FluxPolynomial*` / `Flux*Polynomial`
  - Passthrough machinery  → `FluxPassthrough*`
  - FTC variant            → `Flux(FTC|FTCRiemann)`
