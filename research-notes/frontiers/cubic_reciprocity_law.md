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
- **B0 — DONE** (∅-axiom up to allowed `propext`): the `ℤ[ω]` symbol on rational integers ⟺ the
  rational cubic residue, `EisensteinCubicSymbolRational.cubic_symbol_rational_iff`:
  `(↑a/d)₃ = (↑a)^m ≡ 1 (mod d) ⟺ ∃ y, y³ ≡ a (mod p)`.  For `α = ofInt ↑a` the residue generator
  collapses (`im = 0`), so the symbol is the embedded rational power `(↑a)^m` directly — no
  `x`-substitution.  Chain: `ofInt_pow` + `p_dvd_of_dvd_ofInt` (the `d→p` norm transfer) ⟶
  `p ∣ ((↑a)^m−1)`, the ℕ↔ℤ bridge `pow_mod_one_iff_int` ⟶ `a^m%p=1`, then `pow_m_one_iff_cube`.
  This pins the abstract symbol to `ModArith/CubicResidue`'s rational predicate — foundation for the
  supplementary laws.
- **B1 — DONE** (∅-axiom, **PURE**): the Gauss-sum cube `EisensteinGaussCube.gauss_cube`:
  `(g ⋆ (g ⋆ g))(k) = J · Yfun p k` for `k < p` — the group-ring form of `g(χ)³ = p·J`
  (`Yfun = p·e_0 − N`; in `ℤ[ζ_p]` the all-ones `N ↦ 0` recovers `p·J`).  Chain: `conv_assoc` ⟶
  `(g⋆g)⋆g`, `gauss_sq_eq_J_gaussConj` (`g⋆g = J·ḡ`, since `g(χ²)=ḡ` via `chiOmega_reflect` +
  `conj_chiOmega_eq_sq`) under `conv_congr`, `conv_scalar_left` to pull `J` out, `conv_comm` to
  `g⋆ḡ`, then `gauss_conj_eq_Yfun`.  No new ring machinery needed — fully reused `gauss_sq_full`
  + the norm `g⋆ḡ`.
- **B2** the mod-`q` group-ring reduction + the freshman's dream (the new subsystem, step 2).
  - **B2a — DONE** (∅-axiom, **PURE**): `NumberTheory.BinomPrime.prime_dvd_binom` — `q ∣ binom q t`
    for a prime `q` and `0 < t < q`, the **crux of Frobenius**.  Via the absorption identity
    `(n+1)·C(n,k) = (k+1)·C(n+1,k+1)` (`succ_mul_binom`, induction on the Pascal recursion of the
    213-native `binom`) at `n+1=q, k+1=t`: `t·binom q t = q·binom(q−1)(t−1)`, so `q ∣ t·binom q t`;
    with `q ∤ t` (`0<t<q`) the Euclid lemma `nat_prime_dvd_mul` gives `q ∣ binom q t`.  Also
    `binom_zero_right`, `binom_one`.
  - **B2b — DONE** (∅-axiom up to allowed `propext`): the **binomial theorem in `ℤ[ω]`**,
    `EisensteinBinomial.add_pow`: `(a+b)^n = Σ_{k=0}^{n} binom n k · a^k · b^{n−k}` (`sumRange` over
    `[0,n+1)`, coefficient embedded as `cz n k = ofInt (binom n k)`).  Classical Pascal induction:
    distribute `(a+b)^{n+1} = (a+b)^n·(a+b)`, peel one sum from below (`sumRange_succ_bottom`,
    a new reindex lemma) and the other from above, recombine via Pascal `cz_pascal`, boundary terms
    giving `a^{n+1}`, `b^{n+1}`.  Helpers `cz_{zero,diag,pascal}`, `bterm_mul_{a,b}`.  Next: the
    freshman's dream `(a+b)^q ≡ a^q + b^q (mod ofInt q)` — interior terms vanish by
    `prime_dvd_binom` (B2c).
  - **B2c — DONE** (∅-axiom up to allowed `propext`): the **freshman's dream in `ℤ[ω]`**,
    `EisensteinFreshman.add_pow_modEq_prime`: `(a+b)^q ≡ a^q + b^q (mod ofInt q)` for prime `q` —
    the **Frobenius endomorphism mod `q`**.  `add_pow` expands the `q`-th power; the two endpoints
    give `b^q`, `a^q`, and every interior term is `q`-divisible (`ofIntq_dvd_bterm`: `q ∣ binom q t`
    lifts via `ofInt_dvd` to `ofInt q ∣ cz q t`), so the interior sum is `≡ 0` (`dvd_sumRange` +
    `modEq_zero_of_dvd`).  Reusable `ℤ[ω]` dvd toolkit added: `dvd_add`, `dvd_mul_of_dvd_left`,
    `ofInt_dvd`, `dvd_sumRange` (all PURE).  **Next (B2d):** extend the two-term dream to the
    multinomial / group-ring Gauss sum, then the Frobenius congruence `g^q ≡ χ̄(q)·g (mod q)`.
