import E213.Lib.Math.Real213
import E213.Lib.Math.Analysis
import E213.Lib.Math.AxiomSystems
import E213.Lib.Math.Choice
import E213.Lib.Math.Cohomology
import E213.Lib.Math.Diagonal
import E213.Lib.Math.DyadicFSM
import E213.Lib.Math.HodgeConjecture
import E213.Lib.Math.Hyper
import E213.Lib.Math.Infinity
import E213.Lib.Math.Irrational
import E213.Lib.Math.Linalg213
import E213.Lib.Math.CayleyDickson
import E213.Lib.Math.ModArith
import E213.Lib.Math.Modulus
import E213.Lib.Math.Tactic
import E213.Lib.Math.Trajectory
import E213.Lib.Math.PatternCatalog
import E213.Lib.Math.Probability
import E213.Lib.Math.Information
import E213.Lib.Math.Logic
import E213.Lib.Math.Combinatorics
import E213.Lib.Math.CrossDomainUnification
import E213.Lib.Math.ParadigmDomain
import E213.Lib.Math.ParadigmDomainGraded
import E213.Lib.Math.ParadigmDomainGradedRing
import E213.Lib.Math.ResolutionLimit
import E213.Lib.Math.NatHelpers
import E213.Lib.Math.CascadeCalculus
import E213.Lib.Math.Pigeonhole
import E213.Lib.Math.Polynomial213
import E213.Lib.Math.PrimeDescentObservations
import E213.Lib.Math.Cauchy

/-! Spec-as-code entry point for `E213.Lib.Math` — full 213 mathematics library.

Importing this single module pulls in every Math sub-tree umbrella.
The directory tree is the spec; this file is the top-level entry.

## Sub-tree umbrellas

  ### Core analysis foundation
    * `Real213`         — 213-native real-number type + cut algebra
    * `Analysis`        — calculus on top (Differentiation / Integration
                          / FluxMVT / Cauchy / Series / DyadicSearch /
                          ODE / ClassicCalc — 7 chapter sub-directories)
    * `Cauchy`          — Cauchy / Euler / Wallis / Pell sequences
    * `Modulus`         — modulus combinators for cut-level analysis

  ### Algebra + number theory
    * `CayleyDickson`   — Cayley–Dickson layered construction (ZI →
                          Lipschitz → Cayley → Sedenion → ...)
    * `ModArith`        — modular arithmetic (Bézout / GCD / CRT)
    * `Linalg213`       — 213-native linear algebra
    * `Polynomial213`   — coefficient-array polynomial reflection
    * `Hyper`           — hypernumber / large-cardinal-style

  ### Foundations + meta
    * `AxiomSystems`    — Peano / ZFC / classical-analysis-as-Lens
    * `Choice`          — choice-related results (no Classical.choice)
    * `Diagonal`        — diagonal arguments / Cantor-style fixed points
    * `Infinity`        — lens cardinality, Cantor (∅-axiom)
    * `Irrational`      — irrationality without ZFC

  ### Topical sub-trees
    * `Cohomology`      — K_{NS,NT}^{(c)} cohomology + Hodge programme
                          (~100 files post Phase C peer-promotion)
    * `DyadicFSM`       — dyadic / FSM / Pell / Pisano / Trib / Legendre
                          classification engine (116 files; promoted from
                          Cohomology/Dyadic in Phase C1)
    * `HodgeConjecture` — Hodge-conjecture programme (Foundation /
                          Structure / Pairing / Refinement / Toolkit /
                          Bridge / MotivicBridge — 47 files; promoted
                          from Cohomology/HodgeConjecture in Phase C2)
    * `Trajectory`      — sequence-trajectories
    * `PatternCatalog`  — pattern catalog metaformalization (G30)
    * `CascadeCalculus` — cascade-calculus locality / aggregation

  ### Tools + utility
    * `Tactic`          — math-level tactics (HurwitzRing, IntSquare,
                          QuadExtension)
    * `NatHelpers`      — Nat / Int utility lemmas (6 files)
    * `Pigeonhole`      — universal `Fin` pigeonhole infrastructure
    * `ResolutionLimit` — N_U structural-invariant formalization
    * `PrimeDescentObservations` — descent-style observations

## Status

∅-axiom standard on the production critical path.  Pre-existing
API drift on a small set documented in
`research-notes/HIERARCHICAL_PLACEMENT.md` §6.
-/
