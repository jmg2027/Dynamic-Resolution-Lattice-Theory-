# The cubic residue symbol and the Jacobi-sum norm law `N(J) = p`

**Status**: Closed core (the cubic character `(·/π)₃` on `ℤ[ω]` + the Jacobi sum `J(χ,χ)` +
`N(J) = p` + the primary normalisation `J = π`), with a recorded open frontier (the cubic
reciprocity *law* itself, still open).  ∅-axiom; the
arithmetic core is PURE, a few capstones carry only `propext` (Lean-4 kernel base) from ℕ↔ℤ cast /
divisibility-`decide` bookkeeping.

## Overview

For a rational prime `p ≡ 1 (mod 3)` (write `3m = p − 1`), the Eisenstein integers `ℤ[ω]`
(`ω = e^{2πi/3}`) carry a **cubic residue character**.  This chapter is the closed half of the
cubic-reciprocity arc: the character is a genuine `μ₃ = {1, ω, ω²}`-valued multiplicative symbol with
a two-sided Euler criterion, and the **Jacobi sum** `J(χ,χ) = Σ_t χ(t)·χ(1−t)` is a concrete `ℤ[ω]`
integer whose norm is exactly `p`:

> `N(J) = |J|² = J · J̄ = p`.

From `N(J) = p` with `3 ∤ p`, the Jacobi sum is a **primary Eisenstein prime** above `p`: `J` is
prime, `p = J · J̄` splits, and exactly one of its six unit associates is `≡ 2 (mod 3)`.  This pins
`J` to the canonical prime `π` the reciprocity law is stated with.

The companion chapter `quadratic_reciprocity.md` is the degree-2 analogue; `eisenstein_period_arithmetic.md`
develops the `ℤ[ω]` period side.

## Lean source

`lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/` (aggregator `CayleyDickson.lean`) +
`lean/E213/Lib/Math/NumberTheory/ModArith/CubicResidue.lean`, `CubicCharFp.lean`.

## Narrative

### The character as a `μ₃`-valued multiplicative symbol

On `𝔽_p` the character is the computable `ℤ[ω]`-valued function `χ_ω(t) = ω^{dlog_g(t)}`
(`EisensteinCubicCharFp.chiOmega`): `μ₃`-valued (`chiOmega_value`), multiplicative
(`EisensteinCubicCharFpMul.chiOmega_mul`), with the orthogonality `Σ_t χ_ω(t) = 0`
(`EisensteinCharSumZero.chiListSum_totatives_zero`) and its square's orthogonality `Σ χ_ω²= 0`
(`EisensteinCubicCharSq.chiOmega_sq_orth`).  These are the `𝔽_p`-residue facts the exponent side
(`χ̂(i) = ωⁱ`) could not reach.

Lifted to `ℤ[ω]`, the symbol is `(α/d)₃ = α^m mod d` for the norm-`p` residue prime `d`
(`‖d‖² = p`).  It cubes to one (`EisensteinCubicChar.char_cubes_to_one`), is multiplicative
(`char_mul`), takes values exactly in `μ₃` (`EisensteinCubicCharValue.cube_one_value`), and satisfies
the **two-sided cubic Euler criterion**:

- *cube ⟹ trivial character*: `EisensteinCubicChar.cubic_residue_char_one`;
- *trivial character ⟹ cube*: `EisensteinCubicEuler.char_one_implies_cube`.

The hard direction runs through the residue field `ℤ[ω]/(d) ≅ 𝔽_p` being an integral domain
(`EisensteinPrime.norm_prime_euclid`, `residue_no_zero_divisors` — proven from the Euclidean-gcd
dichotomy, **no** excluded middle).  The symbol is **welded to the rational** cubic residue:
`(α/d)₃ = 1 ⟺ p ∣ (r^m − 1)` (`EisensteinCubicWeld.char_one_iff_rational`), and on a rational integer
`a` this is exactly `a` being a cubic residue mod `p` (`EisensteinCubicSymbolRational.cubic_symbol_rational_iff`,
via `ModArith/CubicResidue.pow_m_one_iff_cube`).

### The Gauss sum in the group ring, and `N(J) = p`

The Gauss sum `g(χ) = Σ_t χ_ω(t)·ζ^t` lives in the **free group ring** `R[C_p]` (`R = ℤ[ω]`),
realised as coefficient functions `ℕ → ℤ[ω]` with **convolution** as multiplication
(`EisensteinGroupRing.conv`).  Working coefficient-wise keeps everything ∅-axiom — function equality
would need `funext` (`Quot`-backed), so every identity is a coefficient equation.

Three relations carry the norm law:

1. `g(χ)² = J · g(χ²)` at every coefficient (`EisensteinGaussSqZero.gauss_sq_full`): the Gauss–Jacobi
   identity, with the diagonal `(g⋆g)(0) = 0` from `χ²`-orthogonality.
2. `g(χ) · conj g(χ) = p·e_0 − N` (`EisensteinGaussOffDiagOne.gauss_conj_norm`): the norm element,
   packaged as `Yfun`.
3. `Y ⋆ Y = p · Y` (`EisensteinNormConv.Yfun_conv`).

Reassembling `(g·g) ⋆ (ḡ·ḡ) = p · Y` (`EisensteinGaussNormSq.gg_gbgb_eq`) and reading off the
`e_1`-coefficient two ways (`Yfun 1 = −1 ≠ 0` cancels) gives the headline
`EisensteinJacobiNormLaw.jacobi_norm`:

> `(jacobiSum p m x).normSq = (p : ℤ)`.

### Primary normalisation — `J = π`

`N(J) = p` with `3 ∤ p` (since `p = 3m + 1`) puts `J` in scope of `EisensteinPrimary.exists_unique_primary`:

- `J` is prime (`EisensteinJacobiPrime.jacobi_prime`, via `norm_prime_euclid`);
- `p = J · J̄` splits (`jacobi_splits_p`);
- exactly one unit associate `u·J` is **primary** (`≡ 2 mod 3`) (`EisensteinJacobiPrimary.jacobi_primary`).

So the Jacobi sum is the canonical primary Eisenstein prime above `p` — the `π` the reciprocity law
normalises with.

## Key results

| Theorem | Statement |
|---|---|
| `EisensteinJacobiNormLaw.jacobi_norm` | `‖J(χ,χ)‖² = p` — the norm law |
| `EisensteinJacobiPrime.jacobi_prime` | `J` is prime in `ℤ[ω]` |
| `EisensteinJacobiPrime.jacobi_splits_p` | `p = J · J̄` |
| `EisensteinJacobiPrimary.jacobi_primary` | `J` has a unique primary associate (`J = π`) |
| `EisensteinCubicChar.char_mul` | `(αβ/d)₃ = (α/d)₃·(β/d)₃` |
| `EisensteinCubicChar.cubic_residue_char_one` / `EisensteinCubicEuler.char_one_implies_cube` | cubic Euler criterion (both ways) |
| `EisensteinCubicWeld.char_one_iff_rational` | `(α/d)₃ = 1 ⟺ p ∣ (r^m − 1)` |
| `EisensteinGaussSqZero.gauss_sq_full` | `g(χ)² = J·g(χ²)` (group ring) |

## Open frontier

The **cubic reciprocity law `(π/π')₃ = (π'/π)₃`** itself is open.  The
Gauss-sum cube `g(χ)³ = p·J` is done (`EisensteinGaussCube.gauss_cube`, PURE), and the **Frobenius
engine** — the mod-`q` subsystem — is built coefficient-wise in `R[C_p]`: `q ∣ binom q t`
(`BinomPrime.prime_dvd_binom`), the `ℤ[ω]` and group-ring binomial theorems and freshman's dreams
(`EisensteinBinomial`, `EisensteinConvBinomial`, `EisensteinFreshman`, `EisensteinConvFreshman`), and
the basis convolution `e_t^{⋆q} = e_{tq%p}` (`EisensteinConvBasis`).  What remains: assemble the
Frobenius congruence `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)` (`χ(t)^q = χ̄(t)` + the `tq`-reindex), then
compare `g^N` two ways to land the law.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Algebra.CayleyDickson
python3 ../tools/scan_axioms.py E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw
# jacobi_norm → "does not depend on any axioms" (PURE)
```
