# Session Handoff — Cubic / Eisenstein Reciprocity arc (autonomous)

## Branch
`claude/transport-campaign-progress-dafaoa`.  Full `lake build E213.Lib.Math.Algebra.CayleyDickson`
passes clean.  ∅-axiom standard: PURE where stated; the rest carry **only** `propext` (Lean-4 kernel
base, allowed-not-target per `STRICT_ZERO_AXIOM.md` — from ℕ↔ℤ cast / `Nat.sub` / `ite` bookkeeping).
No `Classical.choice` / `Quot.sound` / `native_decide` / Mathlib anywhere.

## Goal of the arc
**The cubic reciprocity law `(π/π')₃ = (π'/π)₃`** over the Eisenstein integers `ℤ[ω]`.
Roadmap: `research-notes/frontiers/higher_reciprocity_roadmap.md`; the law itself:
`research-notes/frontiers/cubic_reciprocity_law.md` (the live status tracker — **read it first**).

## Phase A — COMPLETE (∅-axiom)
The cubic character on `𝔽_p`, the Jacobi sum, **`N(J)=p`** (`EisensteinJacobiNormLaw.jacobi_norm`),
`J` prime (`jacobi_prime`), `p = J·J̄` (`jacobi_splits_p`), the primary normalisation `J=π`
(`jacobi_primary`).  Plus the full cubic-residue-symbol theory (μ₃-valued, multiplicative, Euler both
ways, the rational weld).  Details: the `cubic_reciprocity_law.md` frontier "What is already built".

## Phase B — the law itself (IN PROGRESS, this session)
Status tracker = `cubic_reciprocity_law.md`.  Bricks built (all build clean + axiom-scanned):

- **B0** `EisensteinCubicSymbolRational.cubic_symbol_rational_iff` — the `ℤ[ω]` symbol on a rational
  integer ⟺ rational cubic residue.
- **B1** `EisensteinGaussCube.gauss_cube` — `g(χ)³ = p·J` in the group ring (**PURE**).
- **B2** the Frobenius engine (the new mod-`q` subsystem):
  - **B2a** `NumberTheory.BinomPrime.prime_dvd_binom` — `q ∣ binom q t` for `0<t<q` (**PURE**).
  - **B2b** `EisensteinBinomial.add_pow` — the binomial theorem in `ℤ[ω]`.
  - **B2c** `EisensteinFreshman.add_pow_modEq_prime` — freshman's dream `(a+b)^q ≡ a^q+b^q (mod q)`.
  - **B2d** `EisensteinFreshman.sum_pow_modEq_prime` — the `ℤ[ω]` multinomial dream.
  - **B2e** the **group-ring (convolution) Frobenius** (equality is coefficient-wise — no funext):
    - **B2e.1** `EisensteinConvPow` — `delta = e_0`, `convPow` (`⋆`-power), `convOne_left/right`.
    - **B2e.2a** `conv_zero_left/right`, `conv_sumRange_left` (conv linear over finite sums, PURE).
    - **B2e.2b** `convProd_mul_f/g` — `⋆`-exponent raising (PURE).
    - **B2e.2c** `EisensteinConvBinomial.convPow_add_pow` — the **convolution binomial theorem**.
    - **B2e.3** `EisensteinConvFreshman.convPow_add_pow_modEq_prime` — convolution freshman's dream.
    - **B2e.4** `EisensteinConvFreshman.convPow_sum_modEq_prime` — convolution multinomial dream.
    - **B2e.5** `EisensteinConvBasis.basis_conv` (`e_a⋆e_b = e_{(a+b)%p}`, PURE) + `basisPow_eq`
      (`e_t^{⋆q} = e_{tq%p}`); the `ζ^t↦ζ^{tq}` reindex.
    - **B2e.6** `EisensteinConvPow.conv_scalar_right` + `convPow_scalar` (`(c·h)^{⋆q}=c^q·h^{⋆q}`, PURE).

## Next steps (B2e.7 → the Frobenius congruence `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)`)
The pieces are all in hand; remaining assembly:
1. **Per-`t` Gauss term**: `(χ(t)·e_t)^{⋆q}(k) = χ(t)^q·e_{tq%p}(k)` — combine `convPow_scalar` +
   `basisPow_eq`.  And `gauss = Σ_t χ(t)·e_t` coefficient-wise (`gauss i = Σ_t χ(t)·basis t i`,
   `sum_single`); a `convPow_congr` (power respects agreement on `[0,p)`) to swap the base.
2. **Character power** `χ(t)^q = χ̄(t)` for `q ≡ 2 (mod 3)` (μ₃: `χ^q = χ^{q%3} = χ² = χ̄`).
3. **`tq`-reindex** `Σ_t χ̄(t)·e_{tq%p} = χ̄(q)·g` (permutation of `[0,p)` by `t↦tq%p`).
4. Assemble `g^{⋆q} ≡ χ̄(q)·g (mod q)` via `convPow_sum_modEq_prime`.

Then the **law**: compute `g^N` two ways (`g³=pJ` from B1, Frobenius from B2e), compare μ₃ values
using the primary normalisation (`jacobi_primary`).  See `cubic_reciprocity_law.md` "What remains".

## Operating notes (traps hit this session)
- `R[C_p]` equality is **coefficient-wise** (`conv p f g k = …`); function equality needs `funext`
  (`Quot.sound`) — forbidden.  Every convolution identity is `∀ k < p, …`.
- `binom n 0` is **not** `rfl`-reducible with `n` a variable (Pascal recursion splits on the first
  arg) — use `binom_zero_right`.
- `convPow_succ` is `rfl`; the `fun i => conv … i ≡ convPow … (n+1)` defeq is closed by
  `conv_congr … (fun _ _ => rfl)`, not by `rw`'s auto-`rfl`.
- The `ℤ[ω]` binomial / Frobenius tail is a verbatim template: `add_pow` ⟶ `convPow_add_pow`,
  `add_pow_modEq_prime` ⟶ `convPow_add_pow_modEq_prime`, `sum_pow_modEq_prime` ⟶
  `convPow_sum_modEq_prime` (same proof skeleton, ring ops → conv ops).
- propext is fine (allowed-not-target); chase PURE only when cheap (e.g. `le_of_dvd_pos` over core
  `Nat.le_of_dvd`).
