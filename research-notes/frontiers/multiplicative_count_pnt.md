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
    to actually *inhabit* `PrimeDensityToZero` — needs a genuine Chebyshev bound
    (`π(N) = O(N/ln N)`), the irreducible analytic cost.  PNT proper
    (`π(N)·ln N/N → 1`) needs `ln` as a `Real213` cut (in `ExpLog`) + the ratio
    sequence — same certificate shape at the `1`-cut.

## Next concrete step

`primePi` (item 1) CLOSED.  **Infinitude DONE**: `exists_prime_gt` (∀ N, ∃ prime
> N, Euclid via N!+1; local `fact`, `dvd_fact`) — the qualitative `π(N) → ∞` as a
pointing.  Remaining item-2 targets: (a) `π` unboundedness as a Nat statement
(`∀ k, ∃ n, k ≤ primePi n` — from `exists_prime_gt` + `primeIndicator_eq_one_iff`
+ monotonicity); (b) a Chebyshev-type *finite* upper/lower bound pointing at PNT;
(c) tie `factorization_bounded`'s prime-list length to `primePi`.  PNT itself
stays the asymptotic horizon.
