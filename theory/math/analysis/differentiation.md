# Analysis — Differentiation

**Status**: Closed.  Source of truth (∅-axiom):
`lean/E213/Lib/Math/Analysis/Differentiation/` (14 files);
structural map in that directory's `INDEX.md`.

## The idea

Differentiation in 213 is **modulus-tracked**: there is no limit and no
ε-δ.  A function on Real213 cuts is differentiable when it carries an
*explicit derivative function* together with a **modulus** — a
`Nat → Nat` that says, for each requested output precision, how much
input resolution the difference quotient needs to reach it.  The
derivative is not the value of a vanishing limit; it is the witness that
the difference quotient *closes* at a computable rate.  This is the same
move the rest of the analysis cluster makes (`theory/math/modulus.md`):
an existential over ε is replaced by a function that produces the
resolution, so every statement stays constructive and ∅-axiom.

The predicate `IsDifferentiable` (`Differentiable.lean`) extends the
smoothness filter `IsSmooth` (`Smooth.lean`, the `C^∞` predicate) with
that derivative-plus-modulus data; the per-point form is
`DifferentiableAt` (`DifferenceQuotient.lean`).  A differentiable
function therefore knows both *what* its derivative is (the
`IsDifferentiable.derivative` field, with `rfl`-clean closed forms in
`DerivativeForms.lean`) and *how fast* the secant slopes resolve to it.

## What is derived

**The polynomial tower and its sharp modulus.**  Concrete instances are
built for `x^n` across degrees 1–16 (`DifferentiableInstances.lean`).
Their derivative modulus follows the sharp pattern `(n-1)·k`
(`ConcreteDerivativeModulus.lean`): the difference quotient of `x^n`
needs `(n-1)·k` bits to deliver `k` bits of slope, mirroring the
arithmetic fact that `d/dx[x^n]` has degree `n-1`.  The *degree drop is
the modulus rate* — the analytic and the combinatorial readings of "one
order lower" coincide.

**Closure under the calculus combinators.**  Differentiability is closed
under the operations that build polynomials and beyond:

- *Affine* — `affineIsDifferentiable` with derivative the constant `a`
  (`affine_derivative_form`, `affineIsDifferentiable_modulus`).
- *Sum* — `d/dx[x² + x] = 2x + 1` and its degree-`n` generalisation
  (`PolySumDerivativeModulus.lean`, `polynomial_sum_derivative_capstone`);
  the modulus of a sum is the combiner of the summands' moduli.
- *Composition (chain rule)* — `DifferentiableCompose.lean`:
  `squareOfSquare`, `squareOfCube`, `cubeOfSquare`, bundled in
  `polynomial_compose_capstone`; the composed modulus is the chain-rule
  contraction of the two input moduli.
- *Midpoint* — `DifferentiableMid.lean`: `mid(f,g)(x) = (f(x)+g(x))/2`
  stays differentiable, the localised average variant.

The bookkeeping that makes these compose without re-deriving Cauchy
estimates each time is isolated once in `ModulusCombiner.lean` — the
single kernel that combines two `HasModulus` witnesses, so every
combinator above is a one-line application rather than a fresh
ε-δ chase.

**Derivative depth = resolution depth.**  `DerivativeDepth.lean` and
`ResolutionDepth.lean` read the derivative's `linearityModulus` as a
*resolution depth*: the number of bits of input the linear part consumes
per output bit.  This is the same quantity the divergence-depth arc
(`theory/math/analysis/divergence_depth_characterization.md`) counts on
sequences — here on the smooth side — and it runs parallel to the
gauge-coupling resolution depth on the physics branch
(`Physics/Foundations/ResolutionDepth`), the same "how many refinement
steps" count read in two domains.

**Mean Value Theorem.**  The MVT lives in the FTC/flux sibling
`Analysis/FluxMVT/` (`mvt_exists_at`, bundled `mvt_witness_capstone_at`):
on a dyadic bracket the slope is attained, in witness form, with the
witness carrying its own modulus.

## Reading

A derivative is a *pointing at how a function changes*, and its modulus
is the resolution that pointing requires — the calculus read in the same
resolution-aware grammar as the rest of 213.  Nothing here appeals to an
exterior limit: the derivative function and its modulus are the whole
content, and the difference quotient converging to it is a theorem about
rates, not an unreachable ideal.

## Connection

- `theory/math/analysis/integration.md` — the ∫ side; FTC closes the loop
- `theory/math/analysis/minimal_root.md` — DyadicSearch sibling
- `theory/math/modulus.md` — explicit moduli (no ε-δ)
- `theory/math/real213.md` — Real213 cut carrier
