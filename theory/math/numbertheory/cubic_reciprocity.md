# Cubic reciprocity — both cases, ∅-axiom

**Status**: **Closed.**  Both cases of the cubic reciprocity law are formalized at the strict
`∅`-axiom standard (`#print axioms → "does not depend on any axioms"` — no `propext`, no
`Classical`, no Mathlib).  To the best of a deep-research survey, **no proof-assistant
formalization of cubic reciprocity exists anywhere** (Mathlib carries only the Jacobi/Gauss-sum
infrastructure and quadratic reciprocity), so this is novel.

## Overview

For a rational prime `p ≡ 1 (mod 3)` the Eisenstein integers `ℤ[ω]` (`ω = e^{2πi/3}`) carry a
cubic residue character `(·/π)₃`, `μ₃ = {1, ω, ω²}`-valued.  The companion chapter
`cubic_residue_and_jacobi_sum.md` closes the *foundations*: the character, the Jacobi sum
`J = J(χ,χ)` with `N(J) = p`, and the primary normalisation `J = π`.  **This** chapter closes the
*reciprocity law* itself — the statement that the symbol `(π/·)₃` is symmetric — in its two cases,
distinguished by how the second prime sits over `3`:

- **Inert case** — the second prime is a rational prime `q ≡ 2 (mod 3)`.  Then `q` stays prime in
  `ℤ[ω]` and `ℤ[ω]/(q) ≅ 𝔽_{q²}`, where complex conjugation **is** the `q`-power Frobenius.  The law
  reads `(π/q)₃ = χ(q) = (q/π)₃`, packaged as a well-defined `μ₃` symbol.

- **Split case** — both primes are complex Eisenstein primes `π` (norm `p`), `π'` (norm `pr`), both
  `≡ 1 (mod 3)`.  Now conjugation is **not** a Frobenius of either residue field (it maps
  `ℤ[ω]/(π') → ℤ[ω]/(π̄')`), so the inert engine does not apply.  The law `(π/π')₃ = (π'/π)₃` is
  assembled from **two symmetric Gauss-sum computations** (one per modulus) plus a finite `μ₃`
  cancellation — the genuine cross-modulus heart of cubic reciprocity.

The single engine under both cases is the Gauss-sum cube `g(χ)³ = p·π` (`gauss_cube` + the primary
Jacobi sum) and the `q`-power / `pr`-power Frobenius on the cubic Gauss sum, computed coefficient-wise
in the group ring `R[C_p]` (no `funext`, no `Quot.sound`).

## Lean source

Umbrella: `lean/E213/Lib/Math/Algebra/CayleyDickson.lean` (the Eisenstein cluster).

| Module | Lean path (`…/CayleyDickson/Integer/`) | lines | ∅-axiom |
|---|---|---:|---:|
| `EisensteinCubicReciprocity` | `EisensteinCubicReciprocity.lean` | 119 | 3 PURE |
| `EisensteinInertPrime` | `EisensteinInertPrime.lean` | 155 | PURE |
| `EisensteinInertForm` | `EisensteinInertForm.lean` | 112 | PURE |
| `EisensteinInertCube` | `EisensteinInertCube.lean` | 57 | PURE |
| `EisensteinSplitFermat` | `EisensteinSplitFermat.lean` | 59 | PURE |
| `EisensteinSplitReciprocity` | `EisensteinSplitReciprocity.lean` | 111 | 3 PURE |
| `EisensteinSplitResidueSymbol` | `EisensteinSplitResidueSymbol.lean` | 163 | 5 PURE |
| `EisensteinCharNormSplit` | `EisensteinCharNormSplit.lean` | 108 | 4 PURE |
| `EisensteinConjModEq` | `EisensteinConjModEq.lean` | 40 | 2 PURE |
| `EisensteinMu3Lift` | `EisensteinMu3Lift.lean` | 89 | 2 PURE |
| `EisensteinCubicReciprocitySplit` | `EisensteinCubicReciprocitySplit.lean` | 288 | 6 PURE |

## Narrative

### The shared `μ₃` lift

A cube root of unity is pinned by its residue: a congruence between two `μ₃` elements modulo a prime
of norm `> 3` is an **equality**, because the difference of two distinct cube roots of unity has norm
`3` (`‖ω−1‖² = ‖ω²−1‖² = ‖ω²−ω‖² = 3`) and a prime `≠ 3` cannot divide it.  This is
`EisensteinMu3Lift.mu3_eq_of_modEq` (rational modulus `q`) and `mu3_eq_of_modEq_pi` (Eisenstein-prime
modulus `π'`).  It is what upgrades every Gauss-sum *congruence* into a symbol *equality*.

### The inert case — conjugation is Frobenius

A rational prime `q ≡ 2 (mod 3)` is **prime in `ℤ[ω]`** (`EisensteinInertPrime`): the residue field
`ℤ[ω]/(q) ≅ 𝔽_{q²}` is a field, with the inert obstruction `‖d‖² ≠ q` (`EisensteinInertForm`:
`‖d‖² = (a+b)² − 3ab ≡ (a+b)² (mod 3)` is a square, never `≡ 2`) killing the norm-`q` middle branch.
The cube roots of unity in `𝔽_{q²}` are exactly `{1, ω, ω²}` (`EisensteinInertCube.inert_cube_one_value`).

With the Gauss-sum Frobenius collapse `J^{(q²−1)/3} ≡ χ(q) (mod q)` and the `μ₃` lift,
`EisensteinCubicReciprocity.cubic_reciprocity_law` packages the **cubic residue symbol** `(π/q)₃` as
the unique `μ₃` value congruent to `J^{(q²−1)/3}` mod `q`, and proves it equals the character
`χ(q) = (q/π)₃`.  `cubic_residue_symbol_well_defined` states the same as an explicit existence-and-
uniqueness of the symbol value.

### The split case — two symmetric halves

Both primes are complex.  The second prime `π'` (norm `pr ≡ 1 mod 3`) gives `ℤ[ω]/(π') ≅ 𝔽_{p'}`, the
**prime** field, on which conjugation is not an automorphism.  The arc replaces the inert Frobenius by
the `pr`-power Fermat `z^{pr} ≡ z (mod π')` (`EisensteinSplitFermat`) and runs the same Gauss-sum cube.

The first half is `EisensteinSplitResidueSymbol`:

- `split_residue_cube_one` — `J^{3(s+1)} ≡ 1 (mod π')`, so the symbol `(π/π')₃ := J^{s+1} mod π'`
  (`s+1 = (pr−1)/3`) is `μ₃`-valued (`split_residue_symbol_exists`).
- `split_conj_residue_relation` — `(π̄/π')₃ ≡ χ̄(pr)·(π/π')₃ (mod π')`.  The `J̄`-elimination is done
  **without** an inert-style Frobenius (which fails for split `π'`): multiply the all-Eisenstein
  reciprocity congruence `J^{2(s+1)}·J̄^{s+1} ≡ χ̄(pr)` (`EisensteinSplitReciprocity`) by `J^{s+1}` and
  collapse the cube.

The **cross-modulus synthesis** (`EisensteinCubicReciprocitySplit`) combines this with its mirror.  The
key was recognising that the law is an equality of `μ₃` **elements** living in two different residue
fields, and that the source argument's "conjugate law" `χ_π(ᾱ) = conj χ_π(α)` is *garbled* (it would
force `χ_π(N(π')) = 1` always).  The honest identity is `χ_{conj d}(conj α) = conj(χ_d(α))`
(`EisensteinConjModEq.conj_modEq`): conjugation is a ring hom that **flips the modulus** to `conj d`.

With the symbols `A = (π/π')₃`, `S = (π'/π)₃` and the rational characters `C = χ_{π'}(p)`,
`E = χ_π(pr)` (each a `μ₃` literal, `chiOmega_unit_value_gen`), two ingredients per modulus give two
element equations:

- norm-multiplicativity `χ_{π'}(p) ≡ (π/π')₃·(π̄/π')₃` (`char_norm_mult`, from `p = J·J̄` via
  `jacobi_norm` + `mul_conj_self` and `pow_mul_distrib`), and relation A, combine (`combine_relation`)
  to `C = conj E · A²`;
- the swapped pair gives `E = conj C · S²`.

The finite-group step `mu3_reciprocity_algebra` (`C = conj E·A² ∧ E = conj C·S² ⟹ A = S`, a `3⁴`-case
decision — `conj E = C·S` since `conj(S²) = S` for `μ₃`, then cancel `C` and `S·A² = 1` gives
`S = A^{-2} = A`) closes:

> `split_cubic_reciprocity` : `(π/π')₃ = (π'/π)₃`.

`split_cubic_reciprocity_symbol` restates it self-contained: a **single** cube root of unity `V` is
simultaneously `J^{m₂} ≡ V (mod d₂)` and `J₂^{m} ≡ V (mod d)` — the two symbols, in their two
residue fields, are the *same* `μ₃` element.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `cubic_reciprocity_law` | `EisensteinCubicReciprocity` | inert: `(π/q)₃ = χ(q) = (q/π)₃`, well-defined `μ₃` |
| `cubic_residue_symbol_well_defined` | `EisensteinCubicReciprocity` | the inert symbol exists and is unique |
| `inert_cube_one_value` | `EisensteinInertCube` | cube roots of unity in `𝔽_{q²}` are `{1,ω,ω²}` |
| `split_fermat` | `EisensteinSplitFermat` | `z^{pr} ≡ z (mod π')` (split Fermat) |
| `split_conj_residue_relation` | `EisensteinSplitResidueSymbol` | `(π̄/π')₃ ≡ χ̄(pr)·(π/π')₃ (mod π')` |
| `conj_modEq` | `EisensteinConjModEq` | `A≡B mod d ⟹ conj A≡conj B mod conj d` (the honest conjugate law) |
| `mu3_eq_of_modEq{,_pi}` | `EisensteinMu3Lift` | a `μ₃` congruence is an equality (rational / Eisenstein modulus) |
| `char_norm_mult` | `EisensteinCubicReciprocitySplit` | `χ_{π'}(p) ≡ (π/π')₃·(π̄/π')₃ (mod π')` |
| `mu3_reciprocity_algebra` | `EisensteinCubicReciprocitySplit` | `C=conj E·A² ∧ E=conj C·S² ⟹ A=S` |
| **`split_cubic_reciprocity`** | `EisensteinCubicReciprocitySplit` | **split: `(π/π')₃ = (π'/π)₃`** |
| `split_cubic_reciprocity_symbol` | `EisensteinCubicReciprocitySplit` | one common `μ₃` value `V` is both symbols |

## Provenance

The arc was developed as a frontier (now closed and archived): the inert finish, then the split-prime
both-halves build, then the cross-modulus synthesis.  The synthesis follows Ireland–Rosen ch. 9 / the
Xu REU 2021 §4 exposition — **with the conjugate-law identity corrected** (the source's
`χ_π(ᾱ) = conj χ_π(α)` is garbled; the honest identity `χ_{conj d}(conj α) = conj(χ_d(α))` is
`conj_modEq`).  The full closing derivation that this chapter formalizes is reproduced in the
"Narrative" section above.

## Open frontier

None for the law itself.  Natural extensions (not yet built): the supplementary laws (units `ω`, `1−ω`),
a uniform statement spanning both cases, and removing the explicit primary/coprimality hypotheses by
deriving them from primality.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Algebra.CayleyDickson
python3 ../tools/scan_axioms.py E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicReciprocitySplit
# split_cubic_reciprocity → "does not depend on any axioms" (PURE)
python3 ../tools/scan_axioms.py E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicReciprocity
# cubic_reciprocity_law → "does not depend on any axioms" (PURE)
```
