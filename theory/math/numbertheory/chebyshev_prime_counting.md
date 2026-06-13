# Prime counting — elementary Chebyshev and the PNT density cut

How many primes are there below `N`?  The prime number theorem answers
`π(N) ~ N/ln N` asymptotically; **Chebyshev's theorem** is the finite, elementary
core — `c·N/ln N ≤ π(N) ≤ C·N/ln N` for explicit constants — and the **density
statement** `π(N)/N → 0`.  This chapter records the 213-native reconstruction of
both: the upper bound, the density cut as a `Real213` ε-δ certificate, and the
lower bound.  All strict ∅-axiom.

## 213-native answer

There is **no `π` primitive** and no "prime" primitive.  Primality is the divisor
condition `IsPrime213 p := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`, decided ∅-axiom by
a bounded divisor search (`decPrime`).  `π(N) = primePi N` is then a **count-Lens
reading** (`seed/AXIOM/06_lens_readings.md` §6.7): the sum of the prime indicator
`Σ_{k≤N} [IsPrime213 k]`.

The `ln` that appears in every bound is **not** an imported transcendental.  It is
the continuous shadow of the discrete `exp = Nat.pow` depth: the system `×`
generates monomials over a base set graded by total count (`MultSystem`), `value =
exp(depth)`, so `depth = log(value)` — the per-axis bridge `p^{vp_p n} ≤ n`
(`vp_pow_le_self`) and the aggregate `2^{Ω(n)} ≤ n` (`omega_le_log`).  `floorLog p
N` (the largest `f` with `p^f ≤ N`, `Meta/Nat/FloorLog`) is the exact ∅-axiom
inverse of `pow`; the analytic `ln` is its completion (a `Real213` cut).  No
external ruler is applied (`seed/AXIOM/05_no_exterior.md` §5.1).

The density convergence `π(N)/N → 0` is **not** a limit reached from outside.  Per
`object1_not_surjective`, the residue is reached by no pointing; convergence is a
**modulus** — for each resolution `k`, a threshold `M(k)` past which `π(N)/N <
1/k`, written division-free as `π(N)·k < N` (`RatTendsToZero`).  This is 213's ε-δ
(the same shape as `AbCutSeq.toCauchy`).

## The arc

```
   ×-count          C(2n,n)            window (n,2n]            Chebyshev
  monomials  ──▶  central binom  ──▶  ∏_{n<p≤2n} p ∣ C(2n,n)  ──▶  bounds + density
  (MultSystem)    (factorials)        ≤ 4^n                       (this chapter)
```

### Upper bound (Erdős elementary-Chebyshev)

Each prime in `(n, 2n]` divides the central binomial `C(2n,n)`
(`prime_dvd_central_binom`), they are distinct, so their product divides it
(`listProd_dvd`, the coprimality core `vp_listProd_le_one` + `prime_dvd_listProd_mem`),
and `C(2n,n) ≤ 2^{2n}` caps it.  Counting the window with the growing base `n+1`
(`windowCount_pow_le : (n+1)^{#primes(n,2n]} ≤ 2^{2n}`) and reading off the
floor-log gives the **doubling step**

```
   π(2n) ≤ π(n) + ⌊log_{n+1} 2^{2n}⌋        (primePi_two_mul_le_floorLog)
```

Telescoped up the dyadic ladder `1,2,4,…,2^m` and bounded per-window
(`floorLog_window_term_le : ⌊log_{2^k+1} 4^{2^k}⌋ ≤ 2^{k+1}/k` — the growing base
supplies the `1/k = 1/ln` denominator), this yields the **explicit, computable,
axiom-free** upper bound

```
   π(2^m) ≤ chebBound m = 2 + Σ_{k=1}^{m-1} 2^{k+1}/k = O(2^m/m)
                                            (primePi_pow_two_le_chebBound)
```

with the division-free partial-sum certificate `chebBound_mul_le :
chebBound(m+1)·(m+1) ≤ 6·2^{m+1}` (multiplying through clears the floor-division
non-additivity).

### The density cut (PNT density, ∅-axiom)

Combining the dyadic bound (interpolated to all `N` by
`primePi_le_chebBound_of_le`) with `chebBound_mul_le` inhabits the certificate:

```
   primeDensityToZero : PrimeDensityToZero          (π(N)/N → 0, modulus M(k)=2^{12k})
```

For `N ≥ 2^{12k}`, with `m = ⌊log₂ N⌋` (so `2^m ≤ N < 2^{m+1}`, `m ≥ 12k`):
`π(N) ≤ chebBound(m+1)` and `chebBound(m+1)·(m+1) ≤ 6·2^{m+1}` give `π(N)·k < N`.
`RatTendsToZero.below` then yields convergence under *every* positive rational —
the "open analytic core" the scaffolding had isolated is filled.

### Lower bound (Chebyshev, via Kummer)

The matching direction routes through `2^n ≤ C(2n,n) ≤ (2n)^{π(2n)}`.

- **Left** (`central_binom_ge_two_pow : 2^n ≤ C(2n,n)`): induction via the cleared
  recurrence `C(2n+2,n+1)·(n+1) = 2(2n+1)·C(2n,n)`.
- **Kummer** (`vp_central_binom_le_floorLog : vp_p(C(2n,n)) ≤ ⌊log_p(2n)⌋`): the
  hard analytic core.  From `vp_p(C) + 2vp_p(n!) = vp_p((2n)!)`, **Legendre's
  formula** `vp_p(m!) = Σ_j ⌊m/p^{j+1}⌋` (reused from `Lib/Math/NumberTheory/
  Legendre`), and the per-term floor inequality `⌊2n/d⌋ ≤ 2⌊n/d⌋ + [d ≤ 2n]`
  summed (the indicator sum `= ⌊log_p(2n)⌋` by `lcmExpCount_eq_floorLog`).
  Subtraction-free: `2vp_p(n!)` cancels additively.
- **Right** (`central_binom_le_pow_primePi : C(2n,n) ≤ (2n)^{π(2n)}`): via
  `le_pow_primePi` — `m ≤ B^{π(N)}` when every prime factor of `m` is `≤ N` and
  every prime power `p^{vp_p m} ≤ B`.  The distinct-prime grouping is done
  **inductively** on the prime range (peel the full `p`-power at each prime; the
  count is the `primePi` recurrence) — no explicit product-over-primes object.

Taking `log₂` of `2^n ≤ (2n)^{π(2n)} ≤ (2^{⌊log₂2n⌋+1})^{π(2n)}`:

```
   n ≤ (⌊log₂(2n)⌋ + 1) · π(2n)        (chebyshev_lower)
   ⟺  π(2n) ≥ n / (⌊log₂(2n)⌋ + 1) ≈ n / log₂(2n).
```

### The two-sided order theorem `π(N) = Θ(N/log₂N)`

Both halves cut cleanest at the dyadic points `N = 2^{m+1}`, where
`⌊log₂N⌋ = m+1` (`floorLog_pow_self`).  There `chebyshev_lower` (at `n = 2^m`)
and the upper bound (`chebBound` via `chebBound_mul_le`) line up into one
statement (`chebyshev_order`), explicit constants, division-free:

```
   2^{m+1} ≤ 2·(m+2)·π(2^{m+1})        (lower:  π ≥ N / (2·(log₂N + 1)))
   (m+1)·π(2^{m+1}) ≤ 6·2^{m+1}        (upper:  π ≤ 6·N / log₂N)
```

So `π(N) = Θ(N/log₂N)` — Chebyshev's theorem in its *order* form.  The
intermediate one-sided dyadic bounds `two_pow_le_succ_primePi`
(`2^m ≤ (m+2)·π(2^{m+1})`) and `succ_mul_primePi_pow_two_le`
(`(m+1)·π(2^{m+1}) ≤ 6·2^{m+1}`) are the two factors.

## Lean source

- **Sub-tree**: `lean/E213/Lens/Number/Nat213/` — `MultSystem`, `MultSystemValue`
  (count + upper bound + density), `ChebyshevLower` (lower bound).  Generic
  floor-log infra: `lean/E213/Meta/Nat/FloorLog`.
- **∅-axiom status**: all theorems below `#print axioms → does not depend on any
  axioms`.

| theorem | content |
|---|---|
| `MultSystemValue.windowCount_pow_le` | `(n+1)^{#primes(n,2n]} ≤ 2^{2n}` (window count skeleton) |
| `MultSystemValue.primePi_two_mul_le_floorLog` | doubling step `π(2n) ≤ π(n) + ⌊log_{n+1}4^n⌋` |
| `MultSystemValue.primePi_pow_two_le_chebBound` | `π(2^m) ≤ chebBound m = O(2^m/m)` (explicit upper bound) |
| `MultSystemValue.chebBound_mul_le` | division-free `chebBound(m+1)·(m+1) ≤ 6·2^{m+1}` |
| `MultSystemValue.primeDensityToZero` | **`π(N)/N → 0` certified** (PNT density cut) |
| `MultSystemValue.central_binom_ge_two_pow` | `2^n ≤ C(2n,n)` |
| `ChebyshevLower.vp_central_binom_le_floorLog` | **Kummer** `vp_p(C(2n,n)) ≤ ⌊log_p(2n)⌋` |
| `ChebyshevLower.le_pow_primePi` | `m ≤ B^{π(N)}` from per-prime-power bounds |
| `ChebyshevLower.central_binom_le_pow_primePi` | `C(2n,n) ≤ (2n)^{π(2n)}` |
| `ChebyshevLower.chebyshev_lower` | **lower bound** `n ≤ (⌊log₂(2n)⌋+1)·π(2n)` |
| `ChebyshevLower.chebyshev_order` | **two-sided order** `π(2^{m+1}) = Θ(2^{m+1}/m)` (both halves, explicit constants) |

## What is reached and what is not

Both halves of Chebyshev's theorem `c·N/ln N ≤ π(N) ≤ C·N/ln N` and the density
`π(N)/N → 0` are **finite, computable, ∅-axiom**.  The prime number theorem proper
— `π(N) ~ N/ln N` with constant `1` — stays an **asymptotic horizon**: it is a
`Real213` pointing (the ratio sequence `π(N)·ln N / N → 1`), reached by no finite
certificate, only approximated.  This is not a gap in a derivation but the
`object1_not_surjective` signature: the limit is the convergence, and the
convergence *is* the modulus we built.

**Order vs constant — why the horizon is `Real213`, not `ℕ`.**  The density
collapse (`→ 0`) and the order theorem (`Θ`, the *interval* `[c,C]` with `c≈1/2`,
`C=6`) both live in pure `ℕ`; neither pins a transcendental.  PNT differs *in
kind*: it collapses that interval to the **single point `1`**, and pinning the
constant to exactly `1` *is* a claim about `e`/`ln` — base-dependent
(`π(N)·log₂N/N → log₂e`; `ln` is the unique base giving `1`), equivalently
`lcm(1..N) ~ eᴺ` (the elementary `2^{N−1} ≤ lcm(1..N)` sharpening its base from `2`
to `e`).  So no pure-`ℕ` ratio realizes PNT.  The two-sided shape of the pointing is
recorded ∅-axiom as `MultSystemValue.RatTendsToOne` (the `→ 1` companion of
`RatTendsToZero`) with soundness `RatTendsToOne.within` and validation
`succOverSelf`; inhabiting it for `π`/`ψ`/`lcm` is the open analytic core
(PNT-strength), the transcendental-cut `hsep` pattern.
