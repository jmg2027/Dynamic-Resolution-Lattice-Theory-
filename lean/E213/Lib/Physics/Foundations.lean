import E213.Lib.Physics.Foundations.AtomicConstantsUnique
import E213.Lib.Physics.Foundations.AtomicConstantsParametric
import E213.Lib.Physics.Foundations.AtomicConstantsParametricN3
import E213.Lib.Physics.Foundations.AtomicConstantsParametricFull
import E213.Lib.Physics.Foundations.AtomicConstantsParametricFullIff
import E213.Lib.Physics.Foundations.AtomicSuperCatalog
import E213.Lib.Physics.Foundations.DrltZeroParameters
import E213.Lib.Physics.Foundations.FibonacciAtomic
import E213.Lib.Physics.Foundations.FibonacciExtended
import E213.Lib.Physics.Foundations.FiniteResonanceN
import E213.Lib.Physics.Foundations.GoldenRatio
import E213.Lib.Physics.Foundations.HopHypothesis
import E213.Lib.Physics.Foundations.KoideFormula
import E213.Lib.Physics.Foundations.LensCardinalityFractalLevels
import E213.Lib.Physics.Foundations.MasslessParticles
import E213.Lib.Physics.Foundations.ResolutionDepth
import E213.Lib.Physics.Foundations.TightenBracket
import E213.Lib.Physics.Foundations.UnifiedPattern

/-! Spec-as-code entry point for `E213.Lib.Physics.Foundations`.

  Foundational physics scaffolding — atomic constants, fractal-level
  cardinality, resonance structure.

  ## Fractal-level cardinality (parametric, no privileged level)

    * `LensCardinalityFractalLevels` — per-level vertex counts
                                       `numV L = d^L` (bare combinatorics;
                                       no fractal level is privileged)
    * `ResolutionDepth`             — Basel resolution depth per gauge coupling (α_3, α_2, α_1)
    * `FiniteResonanceN`            — resonance count = N

  ## Atomic-constant catalog

    * `AtomicSuperCatalog`          — every atomic integer in one table
    * `DrltZeroParameters`          — zero-parameter discipline witness
    * `UnifiedPattern`              — unified pattern across observables

  ## Number-theoretic structure

    * `FibonacciAtomic`,
      `FibonacciExtended`           — Fibonacci atomicity
    * `GoldenRatio`                 — φ from atomic integers
    * `KoideFormula`                — Koide-type charged-lepton formula
    * `HopHypothesis`               — hop-counting hypothesis

  ## Bracket tools

    * `TightenBracket`              — bracket-narrowing tactic helper
    * `MasslessParticles`           — massless-particle counting
-/
