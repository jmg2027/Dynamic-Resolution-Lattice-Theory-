import E213.Lib.Math.NumberSystems.Real213
import E213.Lib.Math.Analysis
import E213.Lib.Math.Geometry.AngleStructure
import E213.Lib.Math.Foundations.ArityForcingGeneral
import E213.Lib.Math.Foundations.AxiomSystems
import E213.Lib.Math.Logic
import E213.Lib.Math.Geometry.BipartiteDecomp
import E213.Lib.Math.Geometry.CartesianVsDisjoint
import E213.Lib.Math.Foundations.Choice
import E213.Lib.Math.Cohomology
import E213.Lib.Math.NumberSystems.Complex
import E213.Lib.Math.NumberTheory.DyadicFSM
import E213.Lib.Math.Tactic.Extras
import E213.Lib.Math.Analysis.Functional
import E213.Lib.Math.Geometry.GenerationRule
import E213.Lib.Math.Geometry.GeometrizationConjecture
import E213.Lib.Math.Algebra.GRA
import E213.Lib.Math.Geometry
import E213.Lib.Math.Algebra.Group
import E213.Lib.Math.Cohomology.HodgeConjecture
import E213.Lib.Math.NumberSystems.Hyper
import E213.Lib.Math.NumberSystems.Irrational
import E213.Lib.Math.Geometry.LevelTopology
import E213.Lib.Math.Algebra.Linalg213
import E213.Lib.Math.Algebra.CayleyDickson
import E213.Lib.Math.Algebra.CassiniUnimodular
import E213.Lib.Math.Algebra.FiveFloorUnification
import E213.Lib.Math.Foundations.ResidueForm
import E213.Lib.Math.Analysis.Measure
import E213.Lib.Math.NumberTheory.ModArith
import E213.Lib.Math.Analysis.Modulus
import E213.Lib.Math.Analysis.Multivariable
import E213.Lib.Math.Geometry.NumberGrid
import E213.Lib.Math.Analysis.ODE
import E213.Lib.Math.Geometry.OperationTopology
import E213.Lib.Math.NumberSystems.SignedCut
import E213.Lib.Math.NumberSystems.Slots
import E213.Lib.Math.Tactic
import E213.Lib.Math.Foundations.PatternCatalog
import E213.Lib.Math.Probability
import E213.Lib.Math.Probability.Information
import E213.Lib.Math.Combinatorics.Logic
import E213.Lib.Math.Combinatorics
import E213.Lib.Math.Foundations.CrossDomainUnification
import E213.Lib.Math.Foundations.DualCollapseCapstone
import E213.Lib.Math.Algebra.SelfSimilarityBridge
import E213.Lib.Math.Foundations.ParadigmDomain
import E213.Lib.Math.Foundations.ParadigmDomainGraded
import E213.Lib.Math.Foundations.ParadigmDomainGradedRing
import E213.Lib.Math.Foundations.ResolutionLimit
import E213.Lib.Math.Foundations.ProofISALifts
import E213.Lib.Math.Geometry.Topology
import E213.Lib.Math.Geometry.TriangularTower
import E213.Lib.Math.Foundations.UniverseChain
import E213.Meta.Nat
import E213.Lib.Math.Analysis.CascadeCalculus
import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Lib.Math.Algebra.PolyZ
import E213.Lib.Math.Algebra.Polynomial213
import E213.Lib.Math.NumberTheory.PrimeDescentObservations
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.FourSquare
import E213.Lib.Math.NumberTheory.PolyRoot.FactorTheorem
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.PolyRoot.RootBound
import E213.Lib.Math.NumberTheory.PolyRoot.CyclotomicPoly
import E213.Lib.Math.NumberTheory.PolyRoot.ResidueList
import E213.Lib.Math.NumberTheory.EuclideanDivision
import E213.Lib.Math.NumberTheory.FibZIdentities
import E213.Lib.Math.NumberTheory.FibZValuation
import E213.Lib.Math.NumberTheory.GoldenFieldBridge
import E213.Lib.Math.Analysis.Cauchy
import E213.Lib.Math.Probability.MaxEntropy
import E213.Lib.Math.Algebra.DetSpectrumPoles
import E213.Lib.Math.Algebra.Icosahedral
import E213.Lib.Math.Algebra.Mobius213.Px
import E213.Lib.Math.Algebra.Mobius213.TowerConvergence
import E213.Lib.Math.Algebra.Mobius213GrandUnification
import E213.Lib.Math.Algebra.Mobius213SignatureAxisCatalogPhase2
import E213.Lib.Math.Foundations.GradedRingConfigCountBridge
import E213.Lib.Math.Foundations.ParadigmDomainPhysics
import E213.Lib.Math.Foundations.Search
import E213.Lib.Math.NumberSystems.Padic
import E213.Lib.Math.NumberTheory.IntSqrt
import E213.Lib.Math.NumberTheory.AperyIntegrality
import E213.Lib.Math.NumberTheory.FactorialLcmDvd
import E213.Lib.Math.NumberTheory.LcmBoundMain
import E213.Lib.Math.NumberTheory.Zeta3Numerator

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
    * `Irrational`      — irrationality without ZFC

    Cardinality observables (Cantor, Tower, Countable, BoolSpace, Pair,
    Gödel, Chain, LensCardinality, CardinalityLB) live under
    `Lens.Cardinality` — they are Lens-ring observables of Raw, not
    Lib-tier facts.

  ### Topical sub-trees
    * `Cohomology`      — K_{NS,NT}^{(c)} cohomology + Hodge programme
                          (~100 files)
    * `DyadicFSM`       — dyadic / FSM / Pell / Pisano / Trib / Legendre
                          classification engine (116 files)
    * `GeometrizationConjecture` — 213-Lens reading of
                          Thurston/Perelman Geometrization + d=4
                          exotic-smoothness anomaly (ansatz;
                          1 file, open conjecture)
    * `HodgeConjecture` — Hodge-conjecture programme (Foundation /
                          Structure / Pairing / Refinement / Toolkit /
                          Bridge / MotivicBridge — 47 files; promoted
                          from Cohomology/HodgeConjecture in Phase C2)
    * `PatternCatalog`  — pattern catalog metaformalization 
    * `CascadeCalculus` — cascade-calculus locality / aggregation

  ### Tools + utility
    * `Tactic`          — math-level tactics (HurwitzRing, IntSquare,
                          QuadExtension)
    * `NatHelpers`      — Nat / Int utility lemmas (6 files)
    * `Pigeonhole`      — universal `Fin` pigeonhole infrastructure
    * `ResolutionLimit` — Cantor + Cauchy ∅-axiom type-distinction anchors
    * `PrimeDescentObservations` — descent-style observations

## Status

∅-axiom standard on the production critical path.
-/
