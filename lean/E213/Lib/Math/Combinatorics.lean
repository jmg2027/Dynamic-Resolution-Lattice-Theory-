import E213.Lib.Math.Combinatorics.Binomial
import E213.Lib.Math.Combinatorics.Catalan
import E213.Lib.Math.Combinatorics.CatalanBinomial
import E213.Lib.Math.Combinatorics.FibonacciSums
import E213.Lib.Math.Combinatorics.FibonacciDivisibility
import E213.Lib.Math.Combinatorics.FibonacciGcd
import E213.Lib.Math.Combinatorics.LucasFibonacci
import E213.Lib.Math.Combinatorics.PowerSums
import E213.Lib.Math.Combinatorics.SumReshape
import E213.Lib.Math.Combinatorics.Derangements
import E213.Lib.Math.Combinatorics.Zeckendorf
import E213.Lib.Math.Combinatorics.ZeckendorfUniqueness
import E213.Lib.Math.Combinatorics.Stirling
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
