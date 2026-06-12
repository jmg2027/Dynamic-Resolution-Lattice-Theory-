# Session Handoff — 2026-06-12 (MultSystem: multiplicative count → PNT trajectory)

## Branch
`claude/n-plus-signature-mappings-7yrrk3` — the system `×` makes (monomials
over a base set, graded by count) and its trajectory toward the prime number
theorem.  All ∅-axiom (0 dirty).  Pushed.

## What this branch built

### `E213/Lens/Number/Nat213/MultSystem.lean` (34 PURE)
The structure `×` generates — not "ℕ⁺ with × bolted on" but monomials over a
base set, graded by total count.  Carrier = exponent vector (`Mono`); `×` =
exponent-wise add; `deg` = total count = the projection to ℕ (`deg_mul`: × → +;
`deg_unit`: bases are count-1 atoms).
  - `totalCount_closed` : `Σ_{n≤N} monoCount k n = C(N+k, k)` (free count).
  - `doubleTotal_closed` : both axes cut at N ⇒ `C(2N+1, N)` (central binomial).
  - `doubleSumPos_closed` : 1-indexed `Σ_{k=1}^N Σ_{n=1}^N = C(2N+1,N) − N − 1`.
  - per-base increment, hockey-stick (`hockey`, `hockeyDiag`), `binom` + Pascal.

### `E213/Lens/Number/Nat213/MultSystemValue.lean` (28 PURE)
The prime-valued instance — abstract monomials ARE distinct naturals.
  - `expVal` + `expVal_inj` / `caseA_distinct_naturals` : `C(N+k,k)` degree-≤N
    monomials over k primes are `C(N+k,k)` DISTINCT naturals (unique
    factorization, `vp_separation`).
  - `factorization_exists` (`fromVec`): every n>0 = product of primes.
  - `vp_pow_le_self` : `p^(vp p n) ≤ n` (per-axis exp/log).
  - `omega_le_log` : `2^(Ω n) ≤ n`, i.e. `Ω(n) ≤ log₂ n` (total exp/log skeleton).
  - `factorization_bounded` : prime factors of n are ≤ n ⇒ naturals ≤ N use only
    primes ≤ N, so `k = π(N)` bases suffice.
  - `decDvd` (pure `Decidable (k∣n)`) → `decNoFactor` → `isPrime_iff` →
    `decPrime` (pure `Decidable (IsPrime213 n)`) → `primeIndicator`
    (+ `_eq_one_iff`), **`primePi`** (= π(N)), `primePi_le_self`,
    `primePi_monotone`.  Verified: `primePi [10,20,30,100] = [4,8,10,25]`.
  - **`exists_prime_gt`** : ∀ N, ∃ prime > N (infinitude, Euclid via N!+1;
    local `fact`, `dvd_fact`) = `π(N) → ∞` as a pointing.
  - **`primePi_unbounded`** : ∀ k, ∃ N, k ≤ primePi N — the divergence
    *certificate* (213-native ε-N modulus for π → ∞).

## Certificate idea (originator, this branch)
The PNT horizon should be issued as a **Real213 cut + modulus certificate** =
213's ε-δ.  `AbCutSeq.toCauchy (S)(N)(hc)` completes a cut given a modulus
`N(m,k)`; transcendentals (Wallis-π, Euler-e) supply the modulus as `hsep`.
`primePi_unbounded` is the divergence certificate.  **PNT cut framework DONE**:
`RatTendsToZero` (ε-δ modulus for `a N/b N → 0`) + `.below` (soundness) +
`oneOverN` (validation `1/N→0`) + `PrimeDensityToZero := RatTendsToZero primePi
id`.  Scaffolding ∅-axiom; **inhabiting `PrimeDensityToZero` = the open analytic
core** (Chebyshev/PNT).  **Density ≤ 1/2 DONE**: `primePi_two_mul_le : π(2n) ≤ n`
(only 2 is even-prime, `not_prime_two_mul` + `pair_bound`).  Chebyshev ingredients
DONE: `central_binom_le : C(2n,n) ≤ 4^n` (MultSystem) + `prime_not_dvd_fact :
p ∤ n!` for prime p>n (vp_p(n!)=0).  Next: factorial-binom identity
`C(2n,n)·(n!)² = (2n)!` ⇒ `vp_p(C(2n,n))≥1` for n<p≤2n ⇒ `∏_{n<p≤2n} p ∣ C(2n,n)
≤ 4^n` ⇒ `π(N)=O(N/ln N)` ⇒ density→0 (inhabits `PrimeDensityToZero`).  Erdős
elementary-Chebyshev (multi-step).

## Why ln (pinned)
`exp` = `Nat.pow` = iterated `×` = binary-op tower depth (no transcendental).
`value = exp(depth)` ⇒ `depth = log(value)`.  `ln` in π(N) = continuous shadow
of the discrete `Ω ≤ log₂` skeleton.  Also: corrected stale CLAUDE.md note —
`vp_separation` is proven & ∅-axiom (not "open").

Also: `factorization_bounded` (prime factors of n are ≤ n ⇒ naturals ≤ N use
only primes ≤ N, so k = π(N)); `decDvd` (pure `Decidable (k∣n)`, k>0, via
`n % k`); and **π(N) CLOSED**: `decNoFactor` → `isPrime_iff` → `decPrime`
(pure `Decidable (IsPrime213 n)`) → `primeIndicator` (+ `_eq_one_iff`) →
`primePi`, `primePi_le_self`, `primePi_monotone`.  Verified: `primePi
[10,20,30,100] = [4,8,10,25]`.

## Open thread (frontier: `research-notes/frontiers/multiplicative_count_pnt.md`)
**Next concrete step** (π(N) item 1 now CLOSED): **item 2** — value-bounded count.
Infinitude (`exists_prime_gt`) DONE.  Remaining: `π` unboundedness as a Nat
statement (`∀ k, ∃ n, k ≤ primePi n`); a Chebyshev-type *finite* bound pointing
at PNT; tie `factorization_bounded`'s prime list length to `primePi`.  PNT
`π(N) ~ N/ln N` = asymptotic horizon (pointing), not a ∅-axiom target.

## Propext-avoidance learned this branch (IMPORTANT)
Carry **propext**: `Nat.mul_assoc`, `Nat.dvd_trans`, `Nat.le_of_dvd`,
`Nat.decidable_dvd`, `Nat.le_of_add_le_add_left`, `Bool` `_eq_true` reflection.
Pure: `Nat.add_assoc`, `Nat.mul_comm`, `Nat.mul_le_mul`, `Nat.mul_succ`,
`Nat.le_antisymm`, `Nat.lt_or_ge`, `Nat.decLe`, `searchDiv`.  Use
`NatHelper.mul_assoc`/`mul_left_comm`, `Pow213.le_of_dvd_pos`, `decDvd`,
`NatDiv213.le_of_add_le_add_left_pure`.  Note: a Prop `∨` cannot eliminate into a
`Decidable`/Type goal — branch on Nat values or decidable instances, not Prop
disjunctions.
