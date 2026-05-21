import E213.Lib.Math.Combinatorics.Binomial
import E213.Lib.Math.Combinatorics.Catalan
import E213.Lib.Math.Combinatorics.CatalanExtended
import E213.Lib.Math.Combinatorics.Stirling
import E213.Lib.Math.Combinatorics.GeneratingFunction
import E213.Lib.Math.Combinatorics.Simplex5
import E213.Lib.Math.Combinatorics.Capstone

/-!
# Combinatorics 213 — umbrella

Atomic counting on the 213 substrate.  Builds on existing
`Lib/Physics/Simplex/Counts.lean` (binom), `Lib/Math/DyadicFSM/`
(Pell, Pisano), and `Lib/Physics/AtomicBase/Pairs.lean` (K_{3,2}).
This umbrella adds: Catalan, Stirling, Bell, and formal generating
functions — closing the blueprint's "generating function" gap.
-/
