# 14 — Cohomological Calculus

**Tier:** T0/T1
**Status:** Closed at undergraduate level; 176 Lean modules in
Research/Real213*. Five new findings (F1–F5).
**Lean:** `Research/Real213*.lean` (176 files);
canonical narration in `books/math/analysis213.md`.

## Best current statement

213 has its own analysis. It is not a Mathlib reimplementation; it is a
**new cohomological framework** in which differentiation, MVT, and FTC
are aspects of a single object on a dyadic lattice.

### Ground type

```
Cut := Nat → Nat → Bool
```

`c m k = true` ⟺ "this cut value ≤ m/k". Bishop-style superficially,
dyadic-axiom in fact. ZFC ℝ replaced by `(Nat → Raw) × HasModulus` in
`E213/Math/Foundation.lean`.

### Core findings (F1–F5 from `analysis213.md`)

- **F1 Cohomological calculus.** Differentiation = local divergence,
  MVT = path flux equality, FTC = boundary integral — three aspects
  of one cohomological object (`Real213FluxDivergence`).
- **F2 Setoid bridge.** `cohomEquiv` bridges `cutEq` (pointwise) and
  `propEq` without `Quotient` collapse. Preserves dyadic structure.
- **F3 Sharp (n−1)·k resolution depth.** Polynomial differentiation
  modulus = mathematical degree exactly. Tighter than chain-rule
  generic n·k.
- **F4 Constructive vs classical existence.** `HasDyadicMVTWitness`
  separates dyadic c (e.g., x² → c = 1/2) from non-dyadic (x³ →
  c = 1/√3). Catalogued; class-based propagation.
- **F5 Universal dyadic FTC.** Riemann sample sum closed for
  arbitrary dyadic interval [a/2^E, b/2^E].

### Coverage

176 modules cover: cut algebra, dyadic brackets, IsSmooth (filter, not
default), IsDifferentiable (atomic + combinators), MVT (general +
witness + propagation), FTC (Riemann + antiderivative), ODE (linear,
2nd order), Newton's first/second laws, 7 transcendentals at zero
(exp, sin, cos, tan, sinh, cosh, log).

## 213 sharpening

- Sign = orientation, not arithmetic negation (`FluxCut`).
- Smoothness is a filter — generic continuous-but-non-differentiable
  is the default; smooth requires explicit dyadic linearity modulus.
- Vitali sets, Banach-Tarski impossible by construction (no Choice).
- Non-computable reals impossible by construction (all `Bool`-valued).

## Open / next

- **Cohomology 213 marathon (Phase CA–CF) — next priority.**
  Blueprint at `blueprints/math/15_cohomology_213.md` +
  `15_cohomology_213_phases.md`. Generalizes FluxCut/FluxCochain to
  k-cochains on Δᵈ + bipartite K_{NS,NT}^{(c)}; computes higher
  Bettis (b₂), cup product, Hodge ⋆ at cochain level. Direct physics
  payoff: candidate sixth simplicial invariant for the α_em
  5.4×10⁻⁴ structural gap (Ch. 05). Six phases CA→CF, target dir
  `lean/E213/Math/Cohomology/`.
- General `cutMul (a/b) (c/d)` propEq — search-bound, unsolved.
  Phase B "wall" per `research-notes/E1_real213_analysis_roadmap.md`.
- Multi-variable calculus (Phase C–H).
- Measure theory beyond dyadic.

## Sources

- `books/math/analysis213.md` (canonical narrative)
- `lean/E213/Research/Real213*.lean` (176 modules)
- `lean/E213/Math/Foundation.lean`, `Analysis213.lean`,
  `CutOps.lean`, `Series.lean`, `Continuity.lean`, `Cauchy.lean`.
- `research-notes/E1_real213_analysis_roadmap.md`
