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
1. **`g(χ)³ = p·J`** (the Gauss-sum cube) — **DONE** (`EisensteinGaussCube.gauss_cube`, group-ring form
   `(g⋆(g⋆g))(k) = J·Yfun p k`).
2. **The Frobenius congruence `g(χ)^{⋆q} ≡ χ(q)·g(χ̄) (mod q)`** for a second rational prime `q ≡ 2 mod 3`
   — **DONE** (Phase B2e, `EisensteinConvGaussReindex.gauss_pow_modEq_factored_all`, all coefficients).
3. **Assemble** `(π/π')₃ = (π'/π)₃` by computing `g^N` two ways and comparing μ₃ values, using the
   primary normalisation (`jacobi_primary`) to kill the unit ambiguity.  **This is the remaining work.**

### Toolkit for step 3 (built this session)
- **`EisensteinConvCongruence`** (all PURE): the mod-`M` congruence `ModEq` propagates through `⋆`
  (`conv_modEq_left`/`conv_modEq_right`) and through `⋆`-powers (`convPow_modEq`).  The bridge that
  carries the Frobenius congruence (`mod q`) into products with the cube `g³=p·J` and the norm
  `g⋆ḡ=Yfun` (both `⋆`-identities).
- **`gauss_pow_modEq_factored_all`**: the Frobenius congruence as a full group-ring congruence (every
  coefficient `k<p`), the form step 3 multiplies against the cube/norm relations.

### The genuinely-remaining bricks for step 3
- **`charConj_eq_gaussConj_reflect` — DONE**: `conj χ(k) = gaussConj((p−k)%p)` relates the
  character-conjugate Gauss sum `g(χ̄)` (Frobenius RHS) to the ring-conjugate `gaussConj` (norm factor),
  differing by the reflection `k↦(p−k)%p` (an involution).
- **`gauss_pow_succ_modEq` — DONE**: `g(χ)^{⋆(q+1)}(k) ≡ χ(q)·(g(χ̄)⋆g)(k) (mod q)` (via `convPow_succ`
  + `conv_modEq_left` + `conv_scalar_left`) — pushes the Frobenius congruence one power up so the RHS is
  the Gauss-sum norm `g(χ̄)⋆g`.
- **`gaussConj_eq_charConj` — DONE** (`EisensteinGaussCube`): `gaussConj(k) = conj χ(k)` for `k<p` —
  since `χ(−1)=1` (`p−1` a cube, `chiOmega_reflect`), the ring-conjugate `gaussConj` **is** the
  character-conjugate `g(χ̄)`.  (Stronger than the reflection `charConj_eq_gaussConj_reflect`: an exact
  scalar/identity equality, because `m=(p−1)/3` is even.)
- **`gauss_pow_succ_modEq_Yfun` — DONE**: **`g(χ)^{⋆(q+1)}(k) ≡ χ(q)·Yfun(k) (mod q)`** — evaluates the
  norm RHS via `gaussConj_eq_charConj` + `conv_comm` + `gauss_conj_norm` (`g⋆gaussConj=Yfun`).  The
  **Frobenius side** of the `g^{⋆N}`-comparison, in closed form (`Yfun ↦ p` at `e_0` in `ℤ[ζ_p]`).
- **NEXT**: the **cube side** — `g(χ)^{⋆3}(k) = J·Yfun(k)` (rephrase `gauss_cube`'s `g⋆(g⋆g)` as
  `convPow p g 3`, via `conv_assoc`/`convOne_left`).  Then compare `g^{⋆(q+1)}` vs a cube-based
  evaluation of the same exponent (relating `q+1` to the `3`-structure and the norm `g⋆ḡ=Yfun`),
  extracting the μ₃ unit comparison with `jacobi_primary` (`J=π`) to land `(π/π')₃ = (π'/π)₃`.

Estimated scale: the engine (`N(J)=p`, the Frobenius congruence) is now built; the remaining step 3 is the
μ₃-comparison assembly — smaller than the engine, but still a careful multi-brick argument.

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
    `ofInt_dvd`, `dvd_sumRange` (all PURE).
  - **B2d — DONE** (∅-axiom up to allowed `propext`): the **multinomial (`n`-ary) freshman's dream
    in `ℤ[ω]`**, `EisensteinFreshman.sum_pow_modEq_prime`:
    `(Σ_{i<n} f i)^q ≡ Σ_{i<n} (f i)^q (mod ofInt q)` for prime `q`.  Iterates the two-term dream
    over the finite sum (induction on `n`: each `succ` peels `f n`, applies `add_pow_modEq_prime`
    and the inductive congruence under `+`).  Helper `pow_zero_base_pos`.  This is the
    **coefficient-ring template** for the on-path target.
  - **B2e — IN PROGRESS (the genuinely new large phase):** the **group-ring (convolution) Frobenius**.
    - **B2e.1 — DONE** (∅-axiom up to allowed `propext`): the convolution **identity + power**,
      `EisensteinConvPow`.  `delta = e_0` (basis vector at `0`), `convPow p f n` (`n`-fold `⋆`-power,
      `f^{⋆0}=e_0`), with `convPow_zero`, `convPow_succ`, the left identity law `convOne_left`
      (`(e_0⋆f)(k)=f k` for `k<p`, via `sum_single` + `(k+p)%p=k`), and `convPow_one`.
    - **B2e.2a — DONE** (∅-axiom, **PURE**): convolution **left-linearity over finite sums**,
      `conv_zero_left` (`(0⋆g)(k)=0`) and `conv_sumRange_left`
      (`((Σ_{j<m} F j)⋆g)(k) = Σ_{j<m} (F j ⋆ g)(k)`, induction on `m` from `conv_add_left`).  The
      backbone for distributing a binomial sum inside an outer convolution.
    - **B2e.2b — DONE** (∅-axiom, **PURE**): convolution-power **exponent raising**, the `⋆`-analogs
      of `bterm_mul_a/b`: `convProd_mul_f` (`((f^{⋆j}⋆g^{⋆m})⋆f)(k) = (f^{⋆(j+1)}⋆g^{⋆m})(k)`, via
      `conv_assoc`+`conv_comm`+`convPow_succ`) and `convProd_mul_g`
      (`((f^{⋆j}⋆g^{⋆m})⋆g)(k) = (f^{⋆j}⋆g^{⋆(m+1)})(k)`, `conv_assoc`+`convPow_succ`).  **Next
      (B2e.2c):** assemble the convolution binomial theorem
      `(f⊕g)^{⋆n}(k) = Σ_{j} cz n j · (f^{⋆j}⋆g^{⋆(n−j)})(k)` by Pascal induction (template: `add_pow`,
      now with `conv_add_right` / `conv_sumRange_left` / `convProd_mul_{f,g}` in place of the ℤ[ω]
      ring ops).
    - **B2e.2c — DONE** (∅-axiom up to allowed `propext`): the **convolution binomial theorem**,
      `EisensteinConvBinomial.convPow_add_pow`:
      `(f⊕g)^{⋆n}(k) = Σ_{j=0}^{n} binom n j · (f^{⋆j} ⋆ g^{⋆(n−j)})(k)` for `k<p` (coefficient-wise).
      Same Pascal induction as `add_pow`, with `conv_add_right` (distribute over `f⊕g`), `conv_congr`
      + `conv_sumRange_left` (push the inductive binomial sum through the outer `⋆`),
      `convProd_mul_{f,g}` (raise the `⋆`-exponents), `convOne_{left,right}` (the `e_0` boundaries),
      and `cz_pascal` for the recombination.  The `⋆`-analog of B2b — the group-ring core of Frobenius.
    - **B2e.3 — DONE** (∅-axiom up to allowed `propext`): the **convolution freshman's dream**,
      `EisensteinConvFreshman.convPow_add_pow_modEq_prime`:
      `(f⊕g)^{⋆q}(k) ≡ f^{⋆q}(k) + g^{⋆q}(k) (mod ofInt q)` for prime `q`, `k<p`.  Mirror of
      `add_pow_modEq_prime` with `convPow_add_pow` + the conv boundary terms; interior `binom q j`
      (`0<j<q`) are `q`-divisible (`prime_dvd_binom` → `ofInt_dvd` → `dvd_mul_of_dvd_left`), so the
      interior sum `≡ 0` (`dvd_sumRange` + `modEq_zero_of_dvd`).  Reuses the `ℤ[ω]` dvd toolkit from
      `EisensteinFreshman`.  The Frobenius endomorphism of `R[C_p]` mod `q`.
    - **B2e.4 — DONE** (∅-axiom up to allowed `propext`): the **convolution multinomial dream**,
      `EisensteinConvFreshman.convPow_sum_modEq_prime`:
      `(Σ_{t<n} X t)^{⋆q}(k) ≡ Σ_{t<n} (X t)^{⋆q}(k) (mod ofInt q)` for prime `q`, `k<p` (pointwise
      sum of group-ring elements `X t`).  Iterates the binary dream over the finite sum (template:
      `sum_pow_modEq_prime`); helper `convPow_zero_fun` (`0^{⋆q}=0`) needs `conv_zero_right` (added to
      `EisensteinConvPow`).  Applied to `g(χ)=Σ_t χ(t)·e_t` this gives
      `g^{⋆q} ≡ Σ_t χ(t)^q·e_t^{⋆q} (mod q)` — the first half of the Frobenius congruence.
    - **B2e.5 — DONE** (∅-axiom; `basis_conv`/`conv_basis_index` **PURE**, `basisPow_eq` propext):
      **basis-vector convolution + power**, `EisensteinConvBasis`.  `basis a = e_a = ζ^a` (indicator,
      `e_0 = delta`); `basis_conv` (`(e_a⋆e_b)(k) = e_{(a+b)%p}(k)`, the `C_p` group law, via
      `sum_single` + index condition `conv_basis_index` proved from `add_shift_index`/`mod_add_mod`);
      `basisPow_eq` (`e_t^{⋆q}(k) = e_{(t·q)%p}(k)`, induction + `basis_conv`).  This is the
      `ζ^t ↦ ζ^{tq}` Frobenius reindex.
    - **B2e.6 — DONE** (∅-axiom, **PURE**): the **scalar convolution power**, in `EisensteinConvPow`:
      `conv_scalar_right` (`(f⋆(c·g))(k) = c·(f⋆g)(k)`, the companion of `conv_scalar_left`) and
      `convPow_scalar` (`(c·h)^{⋆q}(k) = c^q·h^{⋆q}(k)`, induction via the two scalar pulls).  Lets a
      scaled basis vector be powered: `(χ(t)·e_t)^{⋆q} = χ(t)^q·e_t^{⋆q}`.
    - **B2e.7 — DONE** (∅-axiom up to allowed `propext`): the **scaled-basis convolution power**,
      `EisensteinConvBasis.scaledBasisPow_eq`: `(c·e_t)^{⋆q}(k) = c^q·e_{(t·q)%p}(k)` (`t,k<p`),
      combining `convPow_scalar` + `basisPow_eq`.  With `c = χ(t)` this is the per-`t` Gauss-sum
      Frobenius term `(χ(t)·e_t)^{⋆q}(k) = χ(t)^q·e_{tq%p}(k)`.
    - **B2e.8 — DONE** (∅-axiom, **PURE**): `EisensteinConvPow.convPow_congr` (the `⋆`-power respects
      agreement on `[0,p)`, induction via `conv_congr`) and `EisensteinConvBasis.gauss_eq_sum_basis`
      (`g(χ)(i) = Σ_{t<p} χ(t)·e_t(i)` for `i<p`, via `sum_single`) — rewriting `gauss = Σ_t χ(t)·e_t`,
      the form `convPow_sum_modEq_prime` consumes.
    - **B2e.9 — DONE** (∅-axiom up to allowed `propext`): the **Gauss-sum Frobenius, first half**,
      `EisensteinConvGaussFrobenius.gauss_pow_modEq`:
      `g(χ)^{⋆q}(k) ≡ Σ_{t<p} χ(t)^q·e_{(t·q)%p}(k) (mod ofInt q)` for prime `q`, `k<p`.  Assembles
      three closed pieces, no new machinery: `gauss_eq_sum_basis` under `convPow_congr` (rewrite
      `g = Σ_t χ(t)·e_t` inside the `⋆`-power), `convPow_sum_modEq_prime` (push the `q`-th `⋆`-power
      through the finite sum), `scaledBasisPow_eq` (evaluate each term `(χ(t)·e_t)^{⋆q} = χ(t)^q·e_{tq%p}`).
    - **B2e.10a — DONE** (∅-axiom, **PURE**): the **μ₃ character-power Frobenius**,
      `EisensteinCubicCharPow.chiOmega_pow_q`: `χ_ω(t)^q = conj χ_ω(t)` for `q ≡ 2 (mod 3)`.  Case
      analysis on the four values `{0,1,ω,ω²}` (`0^q=0` (`q≥1`), `1^q=1`, `ω^q=ω^{q%3}=ω²`,
      `(ω²)^q=ω^q·ω^q=ω`); `conj z = z²` on `μ₃` (`conj_chiOmega_eq_sq`) packages it as `χ^q = χ̄`.
    - **B2e.10b — DONE** (∅-axiom up to allowed `propext`): the **Frobenius congruence up to reindex**,
      `EisensteinConvGaussFrobenius.gauss_pow_modEq_conj`:
      `g(χ)^{⋆q}(k) ≡ Σ_{t<p} χ̄(t)·e_{(t·q)%p}(k) (mod ofInt q)` for prime `q ≡ 2 (mod 3)`, `k<p`.
      Combines `gauss_pow_modEq` (B2e.9) with `chiOmega_pow_q` (B2e.10a) termwise (`sum_congr`).
    - **B2e.11 — DONE** (∅-axiom up to allowed `propext`): the **`t↦tq%p` reindex — the Frobenius
      congruence in closed form**, `EisensteinConvGaussReindex`.  Key simplification: the basis vectors
      `e_{(tq)%p}` are **indicators**, so at a fixed coefficient `k` the sum `Σ_t χ̄(t)·e_{tq%p}(k)`
      collapses to the **single** surviving term — no permutation-sum machinery needed.
      - `gauss_conj_reindex_collapse`: `Σ_{t<p} χ̄(t)·e_{(tq)%p}(k) = χ̄((q⁻¹·k)%p)` (`q⁻¹ = aInv q p`).
        Existence of the surviving index by `aInv_spec` (`reindex_idx`: `(t₀·q)%p = k`), uniqueness by
        `cancel_unit` (injectivity of `t↦tq%p`), extracted with `sum_single`.
      - `gauss_pow_modEq_reindexed` (collapse form): `g(χ)^{⋆q}(k) ≡ χ̄((q⁻¹·k)%p) (mod q)`.
      - `char_conj_reindex_split`: `χ̄((q⁻¹·k)%p) = χ(q)·χ̄(k)` for unit `k` — `chiOmega_mul` +
        `conj_mul` + `χ(q⁻¹) = conj χ(q)` (both invert `χ(q)`; via `chiOmega_mul_conj` + `chiOmega_one`).
      - **`gauss_pow_modEq_factored`** (closed): **`g(χ)^{⋆q}(k) ≡ χ(q)·χ̄(k) (mod q)`** for a prime
        `q ≡ 2 (mod 3)`, unit mod `p`, unit coefficient `0<k<p` — the classical Frobenius congruence of
        the cubic Gauss sum (coefficient-wise `g(χ)^{⋆q} ≡ χ(q)·g(χ̄)`, with `g(χ̄)(k)=χ̄(k)`).

    **The Gauss-sum Frobenius congruence (Phase B2e) is COMPLETE.**  The remaining work is the reciprocity
    law assembly itself (compute `g^N` two ways, compare μ₃ values) — see the section below.
    The Gauss-sum power `g^{⋆q}` lives in `R[C_p]` with convolution `⋆`, and equality there is
    **coefficient-wise** (no funext — `Quot`-backed function equality is forbidden).  So the binary
    + multinomial dreams must be **re-proved for `⋆`** (a parallel of B2b/B2c/B2d in the convolution
    ring): define `convPow`, prove the convolution binomial theorem coefficient-wise (reusing
    `conv_add`, `conv_scalar_left`, `conv_assoc`, `conv_comm`), then the freshman's dream mod `q`.
    Then `g^{⋆q} ≡ Σ_t χ(t)^q · e_{tq%p} (mod q)`, `χ(t)^q = χ̄(t)` (μ₃ + `q≡2 mod 3`) and the `tq`
    reindex give `g^{⋆q} ≡ χ̄(q)·g (mod q)` — the Frobenius congruence.  The `ℤ[ω]` versions above
    are the faithful template; the convolution versions are the remaining work.
