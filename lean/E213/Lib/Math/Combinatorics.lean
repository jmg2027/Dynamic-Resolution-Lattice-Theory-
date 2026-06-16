import E213.Lib.Math.Combinatorics.Binomial
import E213.Lib.Math.Combinatorics.Catalan
import E213.Lib.Math.Combinatorics.CatalanBinomial
import E213.Lib.Math.Combinatorics.BellNumbers
import E213.Lib.Math.Combinatorics.FibonacciSums
import E213.Lib.Math.Combinatorics.FibonacciDivisibility
import E213.Lib.Math.Combinatorics.FibonacciGcd
import E213.Lib.Math.Combinatorics.LucasFibonacci
import E213.Lib.Math.Combinatorics.FibBinomialConvolution
import E213.Lib.Math.Combinatorics.Vandermonde
import E213.Lib.Math.Combinatorics.VandermondeDeterminant
import E213.Lib.Math.Combinatorics.FactorialSum
import E213.Lib.Math.Combinatorics.PascalDiagonalFib
import E213.Lib.Math.Combinatorics.PowerSums
import E213.Lib.Math.Combinatorics.TriangularNumbers
import E213.Lib.Math.Combinatorics.PentagonalNumbers
import E213.Lib.Math.Combinatorics.SumReshape
import E213.Lib.Math.Combinatorics.Derangements
import E213.Lib.Math.Combinatorics.DerangementConvolution
import E213.Lib.Math.Combinatorics.Zeckendorf
import E213.Lib.Math.Combinatorics.ZeckendorfUniqueness
import E213.Lib.Math.Combinatorics.Stirling
import E213.Lib.Math.Combinatorics.StirlingFalling
import E213.Lib.Math.Combinatorics.StirlingFirstKind
import E213.Lib.Math.Combinatorics.EulerianNumbers
import E213.Lib.Math.Combinatorics.Worpitzky
import E213.Lib.Math.Combinatorics.MotzkinNumbers
import E213.Lib.Math.Combinatorics.Josephus
import E213.Lib.Math.Combinatorics.NarayanaNumbers
import E213.Lib.Math.Combinatorics.SchroderNumbers
import E213.Lib.Math.Combinatorics.PartitionNumbers
import E213.Lib.Math.Combinatorics.StirlingOrthogonality
import E213.Lib.Math.Combinatorics.BinomialInversion
import E213.Lib.Math.Combinatorics.SurjectionCount
import E213.Lib.Math.Combinatorics.StirlingExplicit
import E213.Lib.Math.Combinatorics.BellStirling
import E213.Lib.Math.Combinatorics.DerangementInclusionExclusion
import E213.Lib.Math.Combinatorics.StirlingOrthogonality2
import E213.Lib.Math.Combinatorics.LahNumbers
import E213.Lib.Math.Combinatorics.DelannoyNumbers
import E213.Lib.Math.Combinatorics.ZigzagNumbers
import E213.Lib.Math.Combinatorics.QBinomial
import E213.Lib.Math.Combinatorics.QBinomialSymmetry
import E213.Lib.Math.Combinatorics.FibonacciCatalanIdentity
import E213.Lib.Math.Combinatorics.LucasStepGeneral
import E213.Lib.Math.Combinatorics.GeneratingFunction
import E213.Lib.Math.Combinatorics.Simplex5
import E213.Lib.Math.Combinatorics.Capstone
import E213.Lib.Math.Combinatorics.GraphConnectivity
import E213.Lib.Math.Combinatorics.BoolEnum
import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Lib.Math.Combinatorics.CountExistence
import E213.Lib.Math.Combinatorics.RamseyLowerBound
import E213.Lib.Math.Combinatorics.RamseyNamedBound
import E213.Lib.Math.Combinatorics.Sperner
import E213.Lib.Math.Combinatorics.SpernerChains
import E213.Lib.Math.Combinatorics.LymInequality
import E213.Lib.Math.Combinatorics.BollobasSetPair
import E213.Lib.Math.Combinatorics.MultinomialTheorem
import E213.Lib.Math.Combinatorics.BollobasCount
import E213.Lib.Math.Combinatorics.ChainAntichain
import E213.Lib.Math.Combinatorics.Permutations
import E213.Lib.Math.Combinatorics.LinearDependence
import E213.Lib.Math.Combinatorics.ParityInvariant
import E213.Lib.Math.Combinatorics.KonigConditional
import E213.Lib.Math.Combinatorics.IntGridSum

/-!
# Combinatorics 213 — umbrella

Atomic counting on the 213 substrate.  Builds on existing
`Lib/Physics/Simplex/Counts.lean` (binom), `Lib/Math/NumberTheory/DyadicFSM/`
(Pell, Pisano), and `Lib/Physics/AtomicBase/Pairs.lean` (K_{3,2}).
Adds: Catalan, Stirling, Bell, formal generating functions; the `Pigeonhole`
primitive; and the proof-ISA reproductions — `CountExistence` /
`RamseyLowerBound` (COUNT, union bound), `Sperner` (COUNT, the dual —
double-counting / LYM), `LinearDependence` (dimension = COUNT),
`ParityInvariant` (READ ∘ SEPARATE), `KonigConditional` (the boundary).
-/
