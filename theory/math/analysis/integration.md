# Analysis — Integration

**Status**: Closed.  Source of truth (∅-axiom):
`lean/E213/Lib/Math/Analysis/Integration/` (10 files); structural map
in that directory's `INDEX.md`.

## The idea

Integration in 213 is a **finite bracket**, never a limit of partitions.
An integral is a Cut-Riemann sum over an explicit dyadic bracket
(`CutRiemann.lean`, `riemannSumOnSamples`): the domain is sampled at a
chosen resolution and the area is the exact rational sum of the sample
rectangles.  Refining the bracket sharpens the value at a *computable*
rate rather than approaching an exterior real — the same modulus-carrying
stance as the rest of the analysis cluster (`theory/math/analysis/modulus.md`).
The underlying primitive is `fluxAlong` (in the `FluxMVT/` sibling):
accumulation along a bracket, with `fluxAlong_const`, `fluxAlong_id`, and
`fluxAlong_compose` giving the constant, identity, and composite cases.

## What is derived

**The definite integral, three bracket shapes.**  The same Riemann sum is
specialised to the brackets actually used downstream:

- *Dyadic* — `IntegralDyadic.lean` over `dyadicIntervalAB`, with
  `integral_one_dyadic` (∫1 = length) and `integral_dyadic_capstone`.
- *Integer interval* — `IntegralIntInterval.lean`,
  `integral_one_intIntervalAB`, the degenerate `integral_one_intIntervalAA`
  (∫ over `[a,a]` = 0).
- *General interval* — `IntegralGeneralInt.lean`,
  `integral_general_int_capstone`.

These are the brackets the α_em derivation leans on (the Wallis and Basel
sums, `theory/physics/alpha_em/`): the integral cluster is the engine
that turns those bracketed products into ∅-axiom rational bounds.

**The antiderivative path and the FTC.**  A second route computes the
integral through an antiderivative (`Antiderivative.lean`,
`IntegralViaAnti.lean`'s `integralCC` / `toAntiderivative`,
`IndefiniteIntegral.lean`, classical cases in `ClassicAnti.lean`).  The
two routes agree: the forward/backward unit theorems
`integralCC_{id,square,cube}_unit_{forward,backward}_at` evaluate the
antiderivative integral on the polynomial tower and match the Riemann
bracket.  The Fundamental Theorem of Calculus proper is in the `FluxMVT/`
sibling — `ftc_riemann_id_depth_zero`, `ftc_riemann_square_depth_zero_at`,
and the generic `ftc_riemann_generic_via_witness_at`: the Riemann
integral of a derivative recovers the bracket endpoints **at depth zero**
(exactly, no residual modulus), the cut-native statement that ∫ undoes
d/dx.

**Properties.**  Linearity and monotonicity of the bracket integral are
in `IntegralProperties.lean`; `Integration.lean` is the top-level entry
bundling the cluster.

## Reading

An integral here is an *accumulation read off a finite bracket*, and
refining the bracket is a re-pointing at finer resolution — not a passage
to an unreachable limit.  Together with the d/dx side
(`differentiation.md`) it closes the calculus loop inside the
resolution-aware grammar: differentiation drops one resolution order,
integration restores it, and the FTC is the depth-zero identity that the
two are inverse pointings.

## Connection

- `theory/math/analysis/differentiation.md` — the d/dx side; FTC closes the loop
- `theory/physics/alpha_em/precision_derivation.md` — Wallis / Basel brackets
- `theory/math/analysis/minimal_root.md` — DyadicSearch sibling
- `theory/math/analysis/modulus.md` — explicit moduli (no ε-δ)
- `theory/math/numbersystems/real213.md` — Real213 cut carrier
