import E213.Lib.Math.Geometry.AlgebraicGeometry
import E213.Lib.Math.Geometry.Rotation
import E213.Lib.Math.Geometry.TensorCalculus
import E213.Lib.Math.Geometry.DiscreteCurvature
import E213.Lib.Math.Geometry.StewartTheorem
import E213.Lib.Math.Geometry.MetricIdentities
import E213.Lib.Math.Geometry.MetricTypes
import E213.Lib.Math.Geometry.LatticeArea

/-! Spec-as-code entry point for `E213.Lib.Math.Geometry`.

213-native algebraic geometry + rotation primitives.

  * `AlgebraicGeometry` — SL(2, F_5) ≅ 2I, K_{3,2}^{(2)} Betti
    numbers, ℤ-base ceiling (Type D Hurwitz vs ℤ[φ] icosian)
  * `Rotation`          — K_{3,2}^{(2)} bipartite multigraph,
    Möbius P linear algebra, Pell-Fib spiral iteration
  * `TensorCalculus`    — general-`n` Christoffel symbols of the
    first kind (symmetry, metric compatibility), the inverse-free
    rung of general-metric Riemannian tensor calculus
  * `DiscreteCurvature` — discrete differential geometry: Forman/Ollivier
    curvature, discrete Bochner/Bakry-Émery, Lichnerowicz spectral
    bridge, binomial heat kernel, graph surgery, homogeneous Ricci flow
-/
