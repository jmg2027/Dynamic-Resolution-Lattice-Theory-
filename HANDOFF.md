# Session Handoff — 2026-06-12 (Chebyshev: prime window (n,2n] → count bound)

## Branch
`claude/autonomous-marathon-vp-listprod-imkycf` — the system `×` makes (monomials
over a base set, graded by count) and its trajectory toward the prime number
theorem.  All ∅-axiom (0 dirty).  Pushed.

## This session (autonomous marathon, from `vp_listProd_le_one`)
Closed the Erdős elementary-Chebyshev numerator + count bound in
`E213/Lens/Number/Nat213/MultSystemValue.lean` (all ∅-axiom):

- **`listProd_dvd`**: distinct primes each `∣ m` ⇒ `∏ ps ∣ m` (via
  `dvd_of_forall_vp_le`).  Support: `listProd_pos`; **`vp_listProd_le_one`**
  (Nodup prime list ⇒ `vp q (∏ ps) ≤ 1`, squarefree); `prime_dvd_listProd_mem`
  (`q ∣ ∏ primes ⇒ q ∈ ps`, Euclid list form, decidability-free).
- **Prime window `(n,2n]`**: `primesIn lo hi` = primes in `(lo,hi]`, built
  counting `hi` down with decidability-free `Nat.decLt`/`decPrime` splits;
  unfolding lemmas `primesIn_cons/_skip/_empty` (`simp only [primesIn]` + goal-
  side `cases`, pure) drive `mem_primesIn_{le,prime,gt}` + `primesIn_nodup`.
  `central_binom_pos`; **`window_prod_dvd_central_binom`** (`∏_{n<p≤2n} p ∣
  C(2n,n)`); **`window_prod_le`** (`∏ ≤ 2^{2n}`).
- **`windowCount_pow_le : (n+1)^{windowCount n} ≤ 2^{2n}`** — the finite ∅-axiom
  Chebyshev count skeleton (`windowCount n = π(2n)−π(n)`; each window prime `>n`;
  `pow_length_le_prod`).  Verified `windowCount 4=2, 10=4, 50=10`.

**Next** (frontier `multiplicative_count_pnt.md`): ∅-axiom floor-`log₂` on `Nat`
to make `windowCount_pow_le` additive (`windowCount n · log₂(n+1) ≤ 2n`), tie
`windowCount` to `primePi`, sum dyadic windows ⇒ `π(N)=O(N/ln N)` ⇒ inhabit
`PrimeDensityToZero`.

## Prior session (n-plus-signature-mappings branch)

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
DONE: `central_binom_le : C(2n,n) ≤ 4^n` (MultSystem), `prime_not_dvd_fact :
p ∤ n!` for p>n, and **`central_binom_factorial : C(2n,n)·(n!)² = (2n)!`** (the
hard gate, nested induction + `ring_nat`).  **`prime_dvd_central_binom : n<p≤2n ⇒ p ∣ C(2n,n)`** + **`prime_not_dvd_listProd`**
(prime ∉ prime-list ⇒ ∤ product, the coprimality core) DONE.
**`dvd_of_forall_vp_le : (∀ prime q, vp q a ≤ vp q b) → a ∣ b`** (a,b>0; order
companion of vp_separation, in Meta/Nat/VpSeparation) DONE.  Next: `listProd_dvd`
(distinct primes each ∣ m ⇒ listProd ∣ m) via dvd_of_forall_vp_le — needs only
`vp_listProd_le_one` (q prime, nodup primes ⇒ vp q (listProd ps) ≤ 1) + a
case-split + `listProd_pos`.  Then the product `∏_{n<p≤2n} p ∣ C(2n,n) ≤ 4^n`,
bound `#{primes in (n,2n]}` via `n^count < ∏ p ≤ 4^n`, sum dyadic windows ⇒
`π(N)=O(N/ln N)` ⇒ density→0 (inhabits `PrimeDensityToZero`).  (propext-tainted:
also `Nat.add_mul`.)

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
