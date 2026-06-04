# `Lib/Physics/Foundations/` — physics scaffolding

Foundational physics primitives: fractal-level cardinality, atomic
constants, finiteness witnesses, resonance structure, and number-
theoretic atomic-integer patterns (Fibonacci, golden ratio, Koide).

## Files

### Fractal-level cardinality (parametric, no privileged level)
  - `LensCardinalityFractalLevels.lean` — per-level vertex counts `numV L = d^L`
  - `ResolutionDepth.lean`              — Basel resolution depth per gauge coupling (α_3, α_2, α_1)
  - `FiniteResonanceN.lean`             — resonance count = N

### Atomic-constant catalog (6)
  - `AtomicConstantsUnique.lean`           — uniqueness theorems
  - `AtomicConstantsParametric.lean`       — parametric form
  - `AtomicConstantsParametricN3.lean`     — N=3 specialisation
  - `AtomicConstantsParametricFull.lean`   — full parametric
  - `AtomicConstantsParametricFullIff.lean`— iff variant
  - `AtomicSuperCatalog.lean`              — every atomic integer in one table
  - `FalsifierRosterForced.lean`           — the falsifier integers as forced polynomials in (NS,NT,d) (the two forcing iffs ⟹ the roster)

### Discipline / unification (2)
  - `DrltZeroParameters.lean`           — zero-parameter discipline witness
  - `UnifiedPattern.lean`               — unified pattern across observables

### Number-theoretic structure (5)
  - `FibonacciAtomic.lean`,
    `FibonacciExtended.lean`            — Fibonacci atomicity
  - `GoldenRatio.lean`                  — φ from atomic integers
  - `KoideFormula.lean`                 — Koide-type charged-lepton formula
  - `HopHypothesis.lean`                — hop-counting hypothesis

### Tools (2)
  - `TightenBracket.lean`               — bracket-narrowing tactic helper
  - `MasslessParticles.lean`            — massless-particle counting

## Top-level

  - `Foundations.lean` — aggregator with full per-section docstring

## Where to add new files

  - N_U scaffolding         → `NUniverse*` / `FractalLens*`
  - Atomic integer table    → `AtomicConstants*` / `AtomicSuperCatalog`
  - Number-theoretic        → match existing `Fibonacci*` / `Koide*` /
                              `GoldenRatio` style
  - Discipline / unified    → `DrltZeroParameters` or `UnifiedPattern`
