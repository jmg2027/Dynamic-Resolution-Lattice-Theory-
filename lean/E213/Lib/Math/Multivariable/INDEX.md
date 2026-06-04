# Multivariable Calculus 213 — Module Index

Blueprint: `blueprints/math/02_multivariable_213.md` (retired).

## Modules

| File | Topic | Theorems | Status |
|---|---|---|---|
| `MultiCut.lean` | `MultiCut n := Fin n → Cut`, `update`, `multiAdd`, zero/one points | 10 | ∅-axiom |
| `PartialDerivative.lean` | `partialAt f i x` slice; `proj i`; `∂xᵢ/∂xᵢ = 1` (rfl) | 5 | ∅-axiom |
| `Gradient.lean` | `gradient f x`, `divergence_1D`, `divergence_2D`; `gradient_const = const` | 7 | ∅-axiom |
| `MultiIntegral.lean` | `multiCubeUnit n`, `multiVolumeNum` for n=2,3,4 = 1; Fubini for constants | 7 | ∅-axiom |
| `Stokes.lean` | 1D Stokes = `fluxAlong`; n-D Stokes existence skeleton; ddω = 0 via `Nat.sub_self` | 4 | ∅-axiom |
| `Capstone.lean` | 5 cluster witnesses + `total_witness` | 6 | ∅-axiom |
| `Multivariable.lean` | umbrella | — | — |

**Total**: 39 atomic facts, all `#print axioms` ∅.

## 213-native paradigm parallel

  * **n-D point = `Fin n → Cut`**: not ℝⁿ, just indexed cuts.
  * **Partial derivative = single-variable slice**: `partialAt f i x`
    fixes `n−1` coords, varies one.  IsDifferentiable applies
    directly without new machinery.
  * **Gradient/divergence/curl = iterated 1D**: each component is
    a `partialAt` evaluation.  No "vector calculus" primitive
    needed.
  * **Multiple integral = iterated 1D Riemann**: Fubini collapses
    to `rfl` for constant integrand on unit n-cube
    (volume = 1·1·...·1 = 1).
  * **n-D Stokes = iterated `fluxAlong`**: 1D Stokes already in
    `Lib/Math/Analysis/FluxMVT/FluxCochain.lean`; n-D structurally
    iterates per axis.

## Connection to existing infrastructure

  * `Lib/Math/NumberSystems/Real213/{CutSum, CutSumTest}` — cut arithmetic for
    multiAdd.
  * `Lib/Math/Analysis/Differentiation/Differentiable.lean` —
    `IsDifferentiable` applies to each `partialAt` slice.
  * `Lib/Math/Analysis/Integration/IntegralDyadic.lean` —
    `dyadicIntervalAB` lifted to `Fin n →` for n-cube.
  * `Lib/Math/Analysis/FluxMVT/FluxCochain.lean` — `fluxAlong`
    IS 1D Stokes.

## Out of scope (separate continuation)

  * Coordinate change / Jacobian (213-native definition needed).
  * Differential forms (`Λᵏ` exterior algebra; would link to
    Cohomology Cup).
  * Riemannian metric / curvature (cohomological form unclear).
  * Manifold-as-bracket-atlas (requires Topology 213 lift).
