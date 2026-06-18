# `Lib/Math/Cohomology/Examples/` — worked examples + topology comparisons

Concrete computational examples for the 213 cohomology
machinery: Δ⁴ simplex, K_{3,2}^{(c=2)} graph, K₅ comparison,
Betti kernel, encoding bijections, Euler closed-form.

## Files (8)

### Δ⁴ + K examples
  - `SimplexBasis.lean`      — Δ⁴ simplex basis enumeration
  - `K5.lean`                — K₅ complete graph comparison (b₁ = 6)
  - `WhyDimFive.lean`        — why dim = 5 (5²⁵ derivation echo)

### Encoding / Betti
  - `BettiKernel.lean`           — Betti number kernel
  - `EncodingBijection.lean`     — encoding bijection
  - `EncodingBijection52.lean`   — 5²-variant bijection
  - `EulerClosed.lean`           — Euler characteristic closed form

### Comparison
  - `TopologyCompare.lean`       — topology comparison across cases

## Where to add new files

  - New concrete graph / simplex → `<Graph>.lean` / `<Shape>.lean`
  - Betti / Euler                → `Betti*` / `Euler*`
  - Encoding bijection           → `EncodingBijection<...>`
  - Comparison study             → `Topology<...>Compare`

## Companion clusters

  - `Cohomology/Cup/`     — cup product
  - `Cohomology/CupAW/`   — Alexander-Whitney cup
  - `Cohomology/Cochain/` — cochain base
