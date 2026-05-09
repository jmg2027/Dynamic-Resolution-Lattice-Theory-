# G51 — Eisenstein CD Ladder: Mechanical Observations

Following the user's bi-axial classification hypothesis (G50 M3+M4):
construct the CD-doubling tower starting from `ZOmega` (Eisenstein
integers) instead of `Int`, and observe property losses at each layer.

**Methodology**: 213-native — mechanical construction, `#eval` /
`decide` checks, no pre-classification.

## Layers constructed

| Layer | Structure | Dim over ℤ |
|---|---|---|
| 0 | `ZOmega` (= ℤ[ω], ω²+ω+1=0) | 2 |
| 1 | `ZOmegaDouble` = ZOmega × ZOmega | 4 |
| 2 | `ZOmegaQuad` = ZOmegaDouble × ZOmegaDouble | 8 |
| 3 | `ZOmegaOct` = ZOmegaQuad × ZOmegaQuad | 16 |

CD multiplication formula: `(a, b)·(c, d) = (a·c − conj(d)·b, d·a + b·conj(c))`.

## Property observations (sample tests)

| Property | L0 (ZOmega) | L1 (4-dim) | L2 (8-dim) | L3 (16-dim) |
|---|---|---|---|---|
| Commutative | ✓ | ✗ | ✗ | ✗ |
| Associative | ✓ | ✓ | ✗ | ✗ |
| Alternative (left/right) | ✓ | ✓ | ✓ | (not tested) |
| Flexible | ✓ | ✓ | ✓ | (not tested) |
| `norm-mult` (samples) | ✓ | ✓ | ✓ | **✗** |
| `(eᵢ+eⱼ)·(eₖ+eₗ) = 0`? | — | — | — | **0 found** |

### Key concrete observations at L1 (ZOmegaDouble, 4-dim)

- `e₁ = (1,0,0,0)` identity
- `e₂² = -1 - ω` (Eisenstein relation **preserved at upper layer**, NOT collapsed to scalar)
- `e₃² = e₄² = -1`
- `e₂·e₃ = e₄`, `e₃·e₂ = -e₃ - e₄` (non-commutative)

### Key observation at L3 (ZOmegaOct, 16-dim)

Brute-force search over all `(i, j, k, l)` with `i<j, k<l, 0≤i,j,k,l<16`:
- **192 quadruples violate `|uv|² = |u|²·|v|²`** (norm-mult failures)
- **0 quadruples give `uv = 0`** (no simple zero divisors)

## Divergence from standard CD ladder

Standard sedenion ladder (ℝ → ℂ → ℍ → 𝕆 → 𝕊):
- L4 (𝕊, 16-dim) loses norm-mult AND has zero divisors of `(eᵢ+eⱼ)·(eₖ+eₗ) = 0` form.

Eisenstein ladder (ZOmega → ZOmegaDouble → ZOmegaQuad → ZOmegaOct):
- L3 (16-dim) loses norm-mult **without** zero divisors of that simple form.

**Threshold pattern alignment** (L0 → L1 → L2 → L3):
| Loss | Standard ladder | Eisenstein ladder |
|---|---|---|
| Commutativity | L1 (ℂ→ℍ) | L1 (ZOmega→ZOmegaDouble) |
| Associativity | L2 (ℍ→𝕆) | L2 (ZOmegaDouble→ZOmegaQuad) |
| Norm-multiplicativity | L3 (𝕆→𝕊) | L3 (ZOmegaQuad→ZOmegaOct) |
| Zero divisors emerge | L3 (𝕊) | (NOT yet at L3 in this form) |

**Bi-axial classification, observational support**:
- The threshold *INDEX* of property loss is **invariant** between the
  two ladders.
- The *specific algebra* at each level differs (different ring
  structure, different basis relations).
- The *type of failure* at the loss boundary may differ (Eisenstein
  L3 has norm-mult failure WITHOUT simple zero divisors; standard
  sedenion has both).

## Caveats

* All "TRUE" results are **sample-based**, not universal.  Universal
  proofs (e.g., `Algebra213.IntegerNormed213` instance for ZOmegaDouble
  / ZOmegaQuad) would lift these from observations to theorems.
* "0 simple zero divisors" only rules out `(eᵢ+eⱼ)·(eₖ+eₗ) = 0`.  More
  complex linear combinations not searched.
* "Eisenstein conjugation" used the existing `ZOmega.conj` which
  swaps ω ↔ ω².  Different conj choices may give different ladders.

## Conjectures (for later verification)

C1.  **Threshold preservation**: For ANY commutative *-ring base R,
the CD-doubling tower R → CD(R) → CD²(R) → ... loses
{commutativity, associativity, norm-multiplicativity} at indices
{1, 2, 3} respectively.

C2.  **Type-of-failure differentiation**: The specific *form* of
norm-mult failure at L3 depends on the base ring's structure (e.g.,
Eisenstein vs ZI).  The Standard sedenion's `(eᵢ+eⱼ)·(eₖ+eₗ) = 0`
zero-divisor form is base-specific.

If C1 holds, "loss of algebraic property" is genuinely a single
phenomenon parameterized by CD level, with the base ring choice
(2-axis + 3-axis bi-classification) determining the SPECIFIC
algebra at each level but NOT when properties are lost.

This is the structural content of G50.M4 (Threshold Theorem),
empirically supported by Eisenstein ladder.
