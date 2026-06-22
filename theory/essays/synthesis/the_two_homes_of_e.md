# The two homes of `e` — `N! = Π_{i=1}^{N} lcm(1..⌊N/i⌋)`

**Reproduced result.** `e` lives in two places, each long-closed and ∅-axiom in the corpus:

  - the **factorial** home — `e = Σ 1/k!`, the factorial `N!` and its prime content via
    Legendre (`FactorialLcmIdentity`, `CutFactorial`);
  - the **lcm-growth** home — `lcm(1..N) ~ eᴺ`, the Chebyshev/`ψ` side
    (`LcmGrowthChebyshev`, `ChebyshevLower`).

The new content is the **product identity welding them**:

> `N! = Π_{i=1}^{N} lcm(1..⌊N/i⌋)`   (`FactorialLcmProduct.factorial_eq_prod_lcm`).

The factorial *is* the product of the lcm's. ∅-axiom
(`lean/E213/Lib/Math/NumberTheory/FactorialLcmProduct.lean`, 5/5 PURE).

## Why we picked it — from a per-prime bridge to the numbers themselves

The corpus already had the *exponent* bridge between the two homes
(`vp_factorial_eq_sum_vp_lcm`): for every prime `p`,
`vp p (N!) = Σ_{i<N} vp p (lcm(1..⌊N/(i+1)⌋))` — Legendre's prime content of `N!` equals the
summed prime content of the lcm-growth side. That is a genuine cross-domain identity, but it
lives at the level of exponents. The honest next step is to lift it to the **numbers**: are
`N!` and the product of the lcm's literally equal? A cross-domain claim earns the word when it
is a proven equality of the objects, not just of a derived statistic.

## Derivation — match the prime-valuation vectors

The lift needs one structural fact the corpus lacked and which was built for this purpose
(`FTAEquality.eq_of_vp_eq`): **a positive number is determined by its prime valuations** — if
`vp p a = vp p b` for every prime `p` (and `a, b > 0`), then `a = b`. (Proved ∅-axiom from
`vp`-under-division: `vp p (b/p) = vp p b − 1`, `vp q (b/p) = vp q b` for `q ≠ p`, giving
`prodL L ∣ b` from `countOcc q L ≤ vp q b` by peeling a prime, then `≤`-antisymmetry.)

With it, the product identity is immediate. Set `b = Π_{i<N} lcm(1..⌊N/(i+1)⌋)`. The valuation
of a product is the sum of valuations (`vp_prod`, from `vp_mul`), so for every prime `p`:

  `vp p b = Σ_{i<N} vp p (lcm(1..⌊N/(i+1)⌋)) = vp p (N!)`,

the second equality being exactly `vp_factorial_eq_sum_vp_lcm`. Both `N!` and `b` are positive
(`factorial_pos`, `prodTo_pos` over `lcmUpTo_pos`), so `eq_of_vp_eq` concludes `N! = b`.

So the two homes of `e` are welded not by a coincidence of growth rates but by a proven
equality of the integers, valuation by valuation.

## Dual function — what the identity buys

Classically this is a known factorial–lcm identity (the multiplicative dual of Legendre's
formula, the `ψ`/`Λ` bookkeeping behind `lcm(1..N) ~ eᴺ`). Read 213-native, it extends the
breadth/primacy programme into analytic/multiplicative number theory with a *proven* map: the
factorial domain and the lcm-growth domain are one residue read two ways, and the bridge is an
equality of objects, not of a statistic — the standard this corpus holds cross-domain claims
to.

Honest scope (`§8` falsifiability discipline). The growth asymptotics (`lcm(1..N) ~ eᴺ`,
`N! ~ (N/e)ᴺ`) are not re-proved here; this is the exact finite product identity underneath
them. The reusable yield is `eq_of_vp_eq` (FTA's "number = valuation vector" half), now
available for any identity provable by matching prime exponents.

## Cross-frame connections

  - **FactorialLcmIdentity** (`vp_factorial_eq_sum_vp_lcm`): the per-prime bridge this lifts.
  - **FTA uniqueness/equality** (`FTAUniqueness`, `FTAEquality`): the factorization multiset is
    read off `n` by `vp` (uniqueness), and `n` is determined by its `vp`-vector (equality) —
    the two halves of FTA, both ∅-axiom, both valuation-native (no UFD, no permutation).
  - **`e`'s factorial home** (`the_prime_constant_is_archimedean.md`, `CutFactorial`): the
    `Σ 1/k!` side.
  - **Chebyshev/PNT** (`ChebyshevLower`, the `log₂ e` narrowing bracket): the lcm-growth side's
    horizon constant.

## Constructive accessibility

Point at it. The product: `FactorialLcmProduct.factorial_eq_prod_lcm` (with `prodTo`,
`prodTo_pos`, `vp_prod`). The FTA-equality tool: `FTAEquality.eq_of_vp_eq` (with `vp_div_self`,
`vp_div_other`, `dvd_of_countOcc_le_vp`). The per-prime bridge:
`FactorialLcmIdentity.vp_factorial_eq_sum_vp_lcm`. All ∅-axiom (`#print axioms` empty).
