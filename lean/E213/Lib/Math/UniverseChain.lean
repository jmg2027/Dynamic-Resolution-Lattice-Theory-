import E213.Lib.Math.UniverseChain.Atomicity
import E213.Lib.Math.UniverseChain.BipartiteFractal
import E213.Lib.Math.UniverseChain.Decomposition
import E213.Lib.Math.UniverseChain.FiniteContainsInfinite
import E213.Lib.Math.UniverseChain.PairAxes
import E213.Lib.Math.UniverseChain.RawBipartition
import E213.Lib.Math.UniverseChain.RawCountGeneric
import E213.Lib.Math.UniverseChain.RawDepth3
import E213.Lib.Math.UniverseChain.RawDepthCount
import E213.Lib.Math.UniverseChain.RawEnumeration
import E213.Lib.Math.UniverseChain.RawRecurrence
import E213.Lib.Math.UniverseChain.Recursion
import E213.Lib.Math.UniverseChain.Residue
import E213.Lib.Math.UniverseChain.TriangleRecurrence

/-! Spec-as-code entry point for `E213.Lib.Math.UniverseChain`.

  Universe chain — Raw count / depth / enumeration / decomposition
  / bipartite-fractal / atomicity / finite-contains-infinite.

  Theme: the recursive Raw → distinction chain.  Atomic forcing
  (NS = 3, NT = 2, d = 5) and the residue are foundational; the
  parametric vertex-count recursion `numV L = d^L` carries no
  privileged level.
-/
