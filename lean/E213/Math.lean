import E213.Math.Real213
import E213.Math.Analysis
import E213.Math.AxiomSystems
import E213.Math.Choice
import E213.Math.Cohomology
import E213.Math.Diagonal
import E213.Math.Hyper
import E213.Math.Infinity
import E213.Math.Irrational
import E213.Math.Linalg213
import E213.Math.CayleyDickson
import E213.Math.ModArith
import E213.Math.Modulus
import E213.Math.Tactic
import E213.Math.Trajectory
import E213.Math.PatternCatalog
import E213.Math.ResolutionLimit
import E213.Math.NatHelpers
import E213.Math.CascadeCalculus
import E213.Math.Pigeonhole
import E213.Math.Polynomial213
import E213.Math.PrimeDescentObservations
import E213.Math.Foundation
import E213.Math.CutOps
import E213.Math.Cauchy
import E213.Math.Series
import E213.Math.Continuity
import E213.Math.Generic

/-! Spec-as-code entry point for `E213.Math` — full 213 mathematics library.

Importing this single module pulls in **every working Math sub-tree**
(post-session 27 cleanup + this session's M1–M6 reorganization).

## Sub-tree umbrellas

  ### Core analysis (Real213 + Analysis split, M5)
    * `Real213`  — 213-native real-number type + cut algebra (44 files)
    * `Analysis` — calculus on top: Differentiation / Integration /
      FluxMVT / Cauchy / Series / DyadicSearch / ODE / ClassicCalc
      (63 files in 7 chapter sub-directories)

  ### Topical sub-trees
    * `AxiomSystems`     — 213 axiom-system formal definitions
    * `Choice`           — choice-related results (no Classical.choice)
    * `Cohomology`       — K_NS,NT^(c) cohomology (202 files)
    * `Diagonal`         — diagonal arguments / fixed points
    * `Hyper`            — hypernumber-style constructions
    * `Infinity`         — lens cardinality, Cantor (∅-axiom)
    * `Irrational`       — irrationality without ZFC
    * `Linalg213`        — 213-native linear algebra
    * `ModArith`         — modular arithmetic
    * `Modulus`          — modulus combinators
    * `Trajectory`       — sequence-trajectories

  ### Top-level standalone modules
    * `PatternCatalog*`  — 5 pattern-catalog files
    * `ResolutionLimit`  — N_U structural invariant
    * `AddMod213`, `EncodePair213`, `IntHelpers`, `Max213`,
      `NatDiv213`, `Pigeonhole`, `Polynomial213`, `PureNat`,
      `PrimeDescentObservations`, `CascadeCalculus*`

  ### Per-chapter sub-umbrellas (strict subsets of `Real213` /
  `Analysis`; for consumers needing only a slice):
    * `Foundation`, `CutOps`, `Cauchy`, `Series`, `Continuity`, `Generic`

## Excluded (pre-existing breakage, deferred)

  * `CayleyDickson` — deeply nested namespace `ZI.ZI.*` requires
    careful surgical fix
  * `Tactic` — `HurwitzRing` depends on CayleyDickson; load-bearing
    for Cayley algebra work
  * 24 Cohomology files inside `Cohomology/` directory but excluded
    from `Cohomology.lean` umbrella (see umbrella docstring)

## Status

∅-axiom standard on the production critical path.
-/
