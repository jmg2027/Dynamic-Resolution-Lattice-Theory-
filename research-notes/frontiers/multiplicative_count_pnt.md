# Frontier — multiplicative count → PNT horizon (`MultSystem` / `MultSystemValue`)

**Branch**: `claude/n-plus-signature-mappings-7yrrk3`.
**Status**: A-region + exp/log skeleton CLOSED (∅-axiom); B (π counting) + PNT
horizon OPEN.

## The trajectory

The system `×` generates (monomials over a base set, graded by total count);
ℕ is the count-projection.  Goal: trace the *finite exact* path that points at
the prime number theorem, rather than collapsing it to a limit.

### Closed (Lean, ∅-axiom)

`E213/Lens/Number/Nat213/MultSystem.lean`:
  - `totalCount_closed` : `Σ_{n≤N} monoCount k n = C(N+k, k)` (free count).
  - `doubleTotal_closed` : both axes cut at `N` ⇒ `C(2N+1, N)` (central binomial).
  - `doubleSumPos_closed` : 1-indexed `Σ_{k=1}^N Σ_{n=1}^N = C(2N+1,N) − N − 1`.

`E213/Lens/Number/Nat213/MultSystemValue.lean`:
  - `expVal_inj` / `caseA_distinct_naturals` : the `C(N+k,k)` degree-≤N monomials
    over `k` primes are `C(N+k,k)` **distinct naturals** (unique factorization,
    `vp_separation`).
  - `factorization_exists` (`fromVec`) : every `n>0` = product of primes.
  - `vp_pow_le_self` : `p^(vp p n) ≤ n` (per-axis exp/log).
  - `omega_le_log` : `2^(Ω n) ≤ n`, i.e. `Ω(n) ≤ log₂ n` (total exp/log skeleton).
  - `factorization_bounded` : every prime factor of `n` is `≤ n` ⇒ naturals `≤ N`
    use only primes `≤ N`, so `k = π(N)` bases suffice.

### Open

1. **`primePi N` (= π(N), # primes ≤ N) as a counting function.** — **CLOSED**
   (`MultSystemValue.lean`, all ∅-axiom).  Route: `decDvd` (pure `Decidable (k∣n)`
   via `n % k`, avoiding propext-tainted `Nat.decidable_dvd`) → `decNoFactor`
   (recursive `Decidable (∀ d, 2≤d → d<b → ¬d∣n)` on bound `b`) → `isPrime_iff`
   (divisor dichotomy) → `decPrime : Decidable (IsPrime213 n)` (matched directly,
   no `decidable_of_iff` instance search) → `primeIndicator` (+ `_eq_one_iff`),
   `primePi`, `primePi_le_self`, `primePi_monotone`.  Verified computing:
   `primePi [10,20,30,100] = [4,8,10,25]`.
   **Propext minefield recorded**: `Nat.decidable_dvd`, `Nat.mul_assoc`,
   `Nat.dvd_trans`, `Nat.le_of_dvd`, `Bool` `_eq_true` reflection are
   propext-tainted; a Prop `∨` cannot eliminate into the `Decidable` Type (branch
   on Nat values / decidable instances instead).

2. **Value-bounded count = N.**  `#{naturals ≤ N} = N` (trivial) realized as
   monomials over the `π(N)` primes with *value* (not degree) `≤ N`.  The
   degree-count `C(N+k,k)` over-counts (exponential); the value-count is exactly
   `N`.  Bridge = `factorization_bounded` (basis ⊆ primes ≤ N) + value-bound.

3. **PNT horizon `π(N) ~ N/ln N`.**  Asymptotic — NOT ∅-axiom-reachable (a limit /
   pointing, `object1_not_surjective` style; reached by none).  Finite exact
   skeleton that *points* at it: `omega_le_log` (`Ω ≤ log₂`) + per-prime
   `vp_pow_le_self`.  Reachable finite partial results: Chebyshev-type bounds,
   `primePi` recurrences.  Record PNT itself as horizon, not target.

## Why `ln` (the structural answer, already pinned)

`exp` here = `Nat.pow` = iterated `×` = iterated-iterated `+` (binary-op tower
depth), no transcendental.  `log` = the inverse depth count.  `value = exp(depth)`
⇒ `depth = log(value)` (`vp_pow_le_self`, `omega_le_log`).  The analytic
`e^x`/`ln` are the continuous completion (`Real213` cuts = pointings).  `ln` in
`π(N)` is the continuous shadow of the discrete `Ω ≤ log₂` skeleton.

## Certificate approach (Real213) — the 213-native ε-δ

The PNT "horizon" should not stay narrative.  **The modulus IS 213's ε-δ
certificate.**  `AbCutSeq.toCauchy (S) (N : Nat → Nat → Nat) (hc)` completes a
climbing rational sequence to a real cut *given a modulus* `N(m,k)` = "to resolve
bit `(m,k)`, go to layer `N(m,k)`".  For transcendentals (π via Wallis, e via
Euler) the modulus is a **hypothesis** (`hsep` / the "conditional measure-modulus
schema"), and rate certificates (bracket widths) reduce it to per-resolution
arithmetic.  This is exactly how to treat PNT 213-natively:

  - **DONE (divergence certificate)**: `primePi_unbounded : ∀ k, ∃ N,
    k ≤ primePi N` — the ε-N modulus for `π(N) → ∞` (no analytic input needed).
  - **DONE (PNT cut framework)**: `RatTendsToZero a b` (ε-δ modulus for
    `a N / b N → 0`, division-free) + `RatTendsToZero.below` (soundness: under
    every positive rational) + `oneOverN` (validation: `1/N → 0` certified) +
    `PrimeDensityToZero := RatTendsToZero primePi id` (the PNT density cut).  The
    scaffolding + soundness are ∅-axiom; **inhabiting `PrimeDensityToZero` is the
    open analytic core** (Chebyshev/PNT-strength) — the single isolated
    hypothesis, transcendental-cut style.
  - **DONE (density ≤ 1/2)**: `primePi_two_mul_le : π(2n) ≤ n` (Chebyshev start —
    only `2` is even-prime, `not_prime_two_mul`; each `(2m+1,2m+2)` pair holds
    ≤ 1 prime, `pair_bound`).  Density `≤ 1/2`.
  - **Remaining (the analytic core)**: sharpen to `π(N) = o(N)` (density `→ 0`)
    to actually *inhabit* `PrimeDensityToZero`.  Fixed-modulus sieves can't reach
    `0` (density `≥ φ(m)/m > 0`); needs the central-binomial route.
    **Ingredient DONE**: `MultSystem.central_binom_le : C(2n,n) ≤ 4^n`
    (`binom_le_two_pow`); `prime_not_dvd_fact : p ∤ n!` for prime `p > n`
    (`vp_p(n!)=0`, the denominator side); **`central_binom_factorial :
    C(2n,n)·(n!)² = (2n)!`** (the factorial-binom identity, via nested induction
    + `ring_nat` — the hard gate, DONE).  **Next ingredient**: `vp_p(C(2n,n)) ≥ 1`
    for `n < p ≤ 2n` — from `central_binom_factorial` + `vp_mul`: `vp_p((2n)!) =
    vp_p(C(2n,n)) + 2·vp_p(n!) = vp_p(C(2n,n))` (since `vp_p(n!)=0`), and
    `vp_p((2n)!) ≥ 1`.  **DONE**: `prime_dvd_central_binom : n<p≤2n ⇒ p ∣ C(2n,n)`.
    `prime_not_dvd_listProd` (prime ∉ prime-list ⇒ ∤ product, the coprimality
    core) DONE.  **`dvd_of_forall_vp_le : (∀ prime q, vp q a ≤ vp q b) → a ∣ b`**
    (a,b>0; the order companion of `vp_separation`, `Meta/Nat/VpSeparation`) DONE.
    **`listProd_dvd`** (distinct primes each `∣ m` ⇒ `listProd ps ∣ m`, via
    `dvd_of_forall_vp_le`) **DONE**, with `listProd_pos`, **`vp_listProd_le_one`**
    (Nodup prime list ⇒ `vp q (∏ ps) ≤ 1`, squarefree) and `prime_dvd_listProd_mem`
    (`q ∣ ∏ primes ⇒ q ∈ ps`, Euclid list form, decidability-free).  **Prime
    window `(n,2n]` DONE**: `primesIn lo hi` (primes in `(lo,hi]`, decidability-free
    `Nat.decLt`/`decPrime` splits + unfolding lemmas `primesIn_cons/_skip/_empty`
    via `simp only [primesIn]`), `mem_primesIn_{le,prime,gt}` + `primesIn_nodup`,
    `central_binom_pos`, **`window_prod_dvd_central_binom`** (`∏_{n<p≤2n} p ∣
    C(2n,n)`), **`window_prod_le`** (`∏ ≤ 2^{2n}`).  **Count bound DONE**:
    `pow_length_le_prod` (`lo^{len} ≤ ∏` when each factor `≥ lo`), `windowCount n`
    (`= π(2n)−π(n)`), **`windowCount_pow_le : (n+1)^{windowCount n} ≤ 2^{2n}`** —
    the finite ∅-axiom Chebyshev count skeleton (each window prime `> n`).

    **Remaining chunk**: convert `windowCount_pow_le` (multiplicative) to additive
    via a ℕ floor-`log₂`: `windowCount n · log₂(n+1) ≤ 2n`, i.e.
    `windowCount n ≤ 2n / log₂(n+1)`.  Then sum dyadic windows
    `(2^k, 2^{k+1}]` (telescoping `π`) ⇒ `π(N) = O(N/ln N)` ⇒ density `→ 0` ⇒
    inhabit `PrimeDensityToZero`.  Erdős elementary-Chebyshev.  Needs a ∅-axiom
    floor-`log₂` (`Nat`, `2^k ≤ n < 2^{k+1}`) — likely already partially in
    `MultSystemValue` (`omega_le_log` gives `2^{Ω n} ≤ n`).  PNT proper (`·ln N` at
    the `1`-cut) needs `ln` (`Real213.ExpLog`) + the ratio sequence — same
    certificate shape.

## Next concrete step

The Chebyshev numerator + count bound are now closed (`window_prod_le`,
`windowCount_pow_le : (n+1)^{windowCount n} ≤ 2^{2n}`).  **Next**: a ∅-axiom
floor-`log₂` on `Nat` (`log2 n` with `2^{log2 n} ≤ n < 2^{log2 n + 1}` for
`n ≥ 1`) to turn `windowCount_pow_le` additive — `windowCount n · log₂(n+1) ≤ 2n`
— giving the explicit `windowCount n ≤ 2n / log₂(n+1)` count cap.  Then tie
`windowCount` to `primePi` (`windowCount n = primePi (2n) − primePi n`, a `primePi`
telescoping over `primesIn`) and sum dyadic windows to reach `π(N) = O(N/ln N)`,
inhabiting `PrimeDensityToZero`.  PNT proper stays the asymptotic horizon.

Loose secondary targets still open: tie `factorization_bounded`'s prime-list
length to `primePi`; a Chebyshev *lower* bound (`π(2n) − π(n) ≥ …`) for the
matching direction.
