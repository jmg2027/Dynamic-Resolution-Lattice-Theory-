# `Lib/Math/Analysis/Integration/` — definite + indefinite integration

213-native integration on Real213 cuts.  Cut-Riemann sums, dyadic
integral, antiderivative + indefinite integral, FTC bridge.

## Files (10)

### Riemann + dyadic
  - `CutRiemann.lean`           — Cut-Riemann sum base
  - `IntegralDyadic.lean`       — dyadic-bracket integral
  - `IntegralIntInterval.lean`  — integer-interval integral
  - `IntegralGeneralInt.lean`   — general-interval integral

### Antiderivative path
  - `Antiderivative.lean`       — antiderivative predicate
  - `IntegralViaAnti.lean`      — integral via antiderivative
  - `IndefiniteIntegral.lean`   — indefinite-integral combinator
  - `ClassicAnti.lean`          — classical-antiderivative cases

### Properties + top-level
  - `IntegralProperties.lean`   — linearity / monotonicity
  - `Integration.lean`          — top-level integration entry

## Where to add new files

  - New integral form         → `Integral<...>.lean`
  - Antiderivative variant    → `Antiderivative<...>` /
                                 `<...>Anti.lean`
  - Property lemma            → `IntegralProperties.lean`

## Companion clusters

  - `Analysis/Differentiation/`  — d/dx side
  - `Analysis/FluxMVT/`          — FTC / flux-form MVT
