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
import E213.Lib.Physics.Foundations.FiniteUniverse
import E213.Lib.Physics.Foundations.FractalLensCardinality
import E213.Lib.Physics.Foundations.GoldenRatio
import E213.Lib.Physics.Foundations.HopHypothesis
import E213.Lib.Physics.Foundations.KoideFormula
import E213.Lib.Physics.Foundations.LensCardinalityFractalLevels
import E213.Lib.Physics.Foundations.MasslessParticles
import E213.Lib.Physics.Foundations.NResolutionFractalDepth
import E213.Lib.Physics.Foundations.NResolutionFromFractal
import E213.Lib.Physics.Foundations.ResolutionDepth
import E213.Lib.Physics.Foundations.TightenBracket
import E213.Lib.Physics.Foundations.UnifiedPattern

/-! Spec-as-code entry point for `E213.Lib.Physics.Foundations`.

  Foundational physics scaffolding — N_resolution cardinality, atomic
  constants, finiteness witnesses, resonance structure.

  ## N_resolution = d^(d²) = 5²⁵ scaffold

    * `NResolutionFromFractal`        — fractal-lens derivation of 5²⁵
    * `NResolutionFractalDepth`       — depth-as-fractal-level witness
    * `FractalLensCardinality`      — combinatorial enumeration
    * `LensCardinalityFractalLevels` — per-level cardinality lemmas
    * `ResolutionDepth`             — N_U as resolution-limit invariant
    * `FiniteUniverse`              — finiteness from resolution limit
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
