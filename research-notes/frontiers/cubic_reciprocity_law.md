# Frontier — the cubic reciprocity law `(π/π')₃ = (π'/π)₃` (Phase B)

**Status:** open.  Phase A (the Jacobi-sum core) is **COMPLETE** (∅-axiom): the cubic character on
`𝔽_p`, the Jacobi sum, **`N(J)=p`** (`EisensteinJacobiNormLaw.jacobi_norm`), `J` prime
(`jacobi_prime`), `p=J·J̄` (`jacobi_splits_p`), and the primary normalisation `J=π`
(`jacobi_primary`).  This note records what remains for the **law itself**.

## What is already built (the cubic residue symbol)

The cubic residue symbol `χ_d(α) = α^m mod d` (`m=(p−1)/3`, `d` the residue prime, `‖d‖²=p`) is a
**complete μ₃-valued multiplicative character**:
- `EisensteinCubicChar.char_mul` — multiplicative `χ_d(αβ) ≡ χ_d(α)·χ_d(β)`.
- `EisensteinCubicCharValue.cubic_char_value` — `μ₃`-valued (`∈{1,ω,ω²}`).
- `EisensteinCubicChar.char_cubes_to_one` — `χ_d(α)³ ≡ 1`.
- **Euler criterion both ways**: `cubic_residue_char_one` (`α` a cube `⟹ χ_d(α)=1`) and
  `EisensteinCubicEuler.char_one_implies_cube` (`χ_d(α)=1 ⟹ α` a cube).
- `EisensteinCubicCharFp.chiOmega` — the same character read on `𝔽_p` as a computable
  `ℤ[ω]`-valued function, with `chiOmega_mul`, orthogonality `Σχ_ω=0`, etc.

So the *symbol* is done; the *reciprocity relation between two symbols* is the open work.

## What remains — the law's proof (a fresh large machinery)

The classical route (Ireland–Rosen, ch. 9) needs the Gauss sum analysed **modulo a second prime**:
1. **`g(χ)³ = p·J`** (the Gauss-sum cube) — from `g(χ)²=J·g(χ²)` (`gauss_sq_full`, DONE) plus
   `g(χ)·g(χ²)=p` (a norm identity for the `χ²` Gauss sum).  Mostly assemblable from existing pieces.
2. **The Frobenius congruence `g(χ)^q ≡ χ̄(q)·g(χ) (mod q)`** for a second rational prime `q` — needs the
   Gauss sum reduced mod `q` (the `(x+y)^q ≡ x^q+y^q mod q` freshman's-dream in the cyclotomic /
   group-ring carrier).  **This is the new subsystem** (mod-`q` reduction of `R[C_p]`).
3. **Assemble** `(π/π')₃ = (π'/π)₃` by computing `g^N` two ways and comparing μ₃ values, using the
   primary normalisation (`jacobi_primary`) to kill the unit ambiguity.

Estimated scale: comparable to the whole `N(J)=p` campaign (the group-ring machinery is reusable; the
mod-`q` reduction + Frobenius is the genuinely new part).

## First concrete bricks (entry points)
- **B0** connect the `ℤ[ω]` symbol on rational integers to the rational cubic residue:
  `χ_d(ofInt a) ≡ 1 ⟺ a` is a cubic residue mod `p` (lift `cubicChar_one_iff_cube` through `ofInt_pow`
  + `d ∣ ofInt k ⟺ p ∣ k`).  Foundation for stating supplementary laws.
- **B1** `g(χ)³ = p·J` (step 1 above) — reuses the convolution ring + `gauss_sq_full`.
- **B2** the mod-`q` group-ring reduction + the freshman's dream (the new subsystem, step 2).
