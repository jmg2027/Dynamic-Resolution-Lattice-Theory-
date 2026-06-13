# Frontier — Chebyshev lower bound `π(N) ≥ c·N/ln N`

**Branch**: `claude/autonomous-marathon-vp-listprod-imkycf`.
**Status**: OPEN.  The matching direction to the now-closed upper bound /
density cut (`multiplicative_count_pnt`, `primeDensityToZero`).  Completing it
gives both halves of Chebyshev's theorem `c·N/ln N ≤ π(N) ≤ C·N/ln N`.

## The route (elementary, via the central binomial)

```
        2^n  ≤  C(2n,n)  ≤  (2n)^{π(2n)}
```

Take `log₂`: `n ≤ π(2n)·log₂(2n)`, i.e. **`π(2n) ≥ n / log₂(2n)`** — a lower
bound of the right order `N/ln N`.

### Done (∅-axiom, `Lens/Number/Nat213/MultSystemValue`)

- **`central_binom_ge_two_pow : 2^n ≤ C(2n,n)`** — the left inequality.
  Induction via the cleared recurrence `C(2n+2,n+1)·(n+1) = 2(2n+1)·C(2n,n)`
  (from `central_binom_factorial`, cancelling `(n!)²` and one `(n+1)`).

### Open — the right inequality `C(2n,n) ≤ (2n)^{π(2n)}`

`C(2n,n) = ∏_{p ≤ 2n, prime} p^{vp_p(C(2n,n))}`, and **each prime power is
`≤ 2n`** (Kummer): `p^{vp_p(C(2n,n))} ≤ 2n`.  With `≤ π(2n)` distinct primes,
the product is `≤ (2n)^{π(2n)}`.

**The Kummer prime-power bound** `vp_p(C(2n,n)) ≤ floorLog p (2n)` (hence
`p^{vp_p(C(2n,n))} ≤ p^{floorLog p (2n)} ≤ 2n`):

  `vp_p(C(2n,n)) = vp_p((2n)!) − 2·vp_p(n!)`
    `= Σ_i (⌊2n/p^i⌋ − 2⌊n/p^i⌋)`        [Legendre]
    `≤ Σ_{i : p^i ≤ 2n} 1 = floorLog p (2n)`  [each term ∈ {0,1}; vanishes for `p^i > 2n`]

Ingredients that **already exist** (reuse, don't rebuild):
  - **`Legendre.legendre`** (`Lib/Math/NumberTheory/Legendre`): `vp_p(N!) =
    Σ_e ⌊N/p^{e+1}⌋`-style sum.  Also `vp_factorial`, `indLt_sum`.
  - **`floorLog`** + sandwich (`Meta/Nat/FloorLog`): `p^{floorLog p N} ≤ N`.
  - **`Prime213 ≡ IsPrime213`** — *definitionally equal* (`2 ≤ p ∧ ∀ d, d∣p →
    d=1 ∨ d=p`); a proof of one serves for the other.  (`Legendre` uses
    `Prime213`; the central binom uses `IsPrime213`.)
  - The factorization-into-prime-powers product form (`MultSystemValue`
    `expVal`/`fromVec`, or `vp_separation`-style reconstruction).

Steps to close:
  1. `legendre_term_le_one`: `⌊2n/p^{i+1}⌋ − 2⌊n/p^{i+1}⌋ ≤ 1` (per-term).
  2. `vp_central_binom_le_floorLog`: combine Legendre for `(2n)!` and `n!` with
     step 1 ⇒ `vp_p(C(2n,n)) ≤ floorLog p (2n)`.
  3. `prime_pow_dvd_central_binom_le`: `p^{vp_p(C(2n,n))} ≤ 2n`
     (step 2 + `floorLog` sandwich).
  4. `central_binom_le_pow_primePi`: `C(2n,n) ≤ (2n)^{π(2n)}` (product over the
     `≤ 2n` primes; each factor `≤ 2n`; count `≤ π(2n)`).
  5. `primePi_two_mul_ge`: `2^n ≤ (2n)^{π(2n)}` ⇒ `n ≤ π(2n)·floorLog 2 (2n)`
     ⇒ the lower bound (cleared-denominator form, like `chebBound_mul_le`).

### Layering note

`Legendre` lives in `Lib/Math/NumberTheory`; the central binomial lives in
`Lens/Number/Nat213/MultSystemValue`.  A file combining them must sit **above
both**.  Options: (a) a new `Lib/Math/NumberTheory/ChebyshevLower.lean` that
imports `MultSystemValue` (check Lens is importable from Lib); (b) relocate the
central-binomial factorial lemmas to a shared lower layer (`Meta/Nat` or a new
`Lib/Math` module) alongside `Legendre`.  Decide before starting step 1.

### Secondary

A two-sided density (`c ≤ π(N)·ln N / N ≤ C`) once both bounds are in;
cross-check against the lcm-growth route (`LcmGrowthChebyshev`, which has the
parallel `vp(lcm) = floorLog` machinery and is aimed at the same Chebyshev
30-block bound for ζ(3)).
