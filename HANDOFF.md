# Session Handoff — 2026-06-12 (PNT density cut π(N)/N→0 INHABITED ∅-axiom)

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
  Chebyshev count skeleton (`pow_length_le_prod`; each window prime `>n`).
- **`floorLog` relocated** `LcmGrowthChebyshev` → **`Meta/Nat/FloorLog`** (generic
  Nat infra: floor-log `⌊log_p N⌋` + sandwich + general-base pow monotonicity;
  `Lens/` can now import it; consumers open+re-export, `FactorialLcmDvd` untouched).
- **`windowCount_le_floorLog : 1≤n → windowCount n ≤ floorLog (n+1) (2^{2n})`** —
  the additive count cap (`floorLog_ge` on `windowCount_pow_le`).
- **`primePi` tie**: `primePi_add_primesIn_length` (`lo≤hi → π lo + #primes(lo,hi]
  = π hi`), `windowCount_eq` (`π n + windowCount n = π(2n)`), and
  **`primePi_two_mul_le_floorLog : π(2n) ≤ π(n) + floorLog (n+1) (2^{2n})`** — the
  ∅-axiom Chebyshev doubling step.  Verified `π(8)=4, windowCount 8=2, π(16)=6`.
- **Dyadic telescoping**: `def chebSum m = Σ_{k<m} floorLog(2^k+1)(4^{2^k})` +
  **`primePi_pow_two_le_chebSum : π(2^m) ≤ chebSum m`** (iterate the doubling step).
  `chebSum` = the exact finite ∅-axiom Chebyshev upper-bound skeleton.  Verified
  `π(8)=4 ≤ chebSum 3=7, π(16)=6 ≤ chebSum 4=12`.
- **`floorLog` upper-bound infra** (`Meta/Nat/FloorLog`): `floorLog_le_iff`,
  `floorLog_le_of_lt_pow`, `floorLog_antitone_base`, `floorLog_pow_self`.
- **Per-window term** `floorLog_window_term_le : 1≤k → floorLog (2^k+1)(4^{2^k}) ≤
  2^{k+1}/k` (via `floorLog_le_of_lt_pow` + `lt_mul_div_succ`; the growing base
  `2^k+1` supplies the `1/k = 1/ln(base)` denominator — propext dodged with pure
  `div_add_mod`/`pow_mul_pure`).
- **THE CAPSTONE** `primePi_pow_two_le_chebBound : π(2^m) ≤ chebBound m`
  (`= 2 + Σ_{k=1}^{m-1} 2^{k+1}/k = O(2^m/m)`) — the explicit, computable,
  axiom-free Erdős elementary-Chebyshev `π(N)=O(N/ln N)`.  Via `windowBound`
  (pattern-matched, no `ite`) + `term_le_windowBound` + `chebSum_le_chebBound` ∘
  `primePi_pow_two_le_chebSum`.  Verified `π(8)=4≤10, π(1024)=172≤chebBound 10=269`.
  In `CAPSTONE_INDEX.md` (new "Prime counting" section).

- **`chebBound_mul_le`** — division-free partial-sum bound `chebBound(m+1)·(m+1) ≤
  6·2^{m+1}` (= `chebBound m = O(2^m/m)`; multiplying through dodges floor-div
  non-additivity; paired crude `chebBound(m+1) ≤ 2^{m+2}`).
- **THE KEYSTONE** `primeDensityToZero : PrimeDensityToZero` — **`π(N)/N → 0`
  certified ∅-axiom**, the PNT density cut (the scaffolding's "open analytic core")
  CLOSED.  Modulus `M(k)=2^{12k}`; `density_cert_aux` does the arithmetic at level
  `m=⌊log₂N⌋`.  Pure cancellation helpers `mul_lt_mul_right_pure` /
  `lt_of_mul_lt_mul_right_pure` (avoid `Nat.*`'s Classical axioms).  In
  `CAPSTONE_INDEX.md`.

**Chebyshev lower bound** `π(N) ≥ c·N/ln N` (`frontiers/chebyshev_lower_bound.md`,
new file `Lens/Number/Nat213/ChebyshevLower.lean`) — via `2^n ≤ C(2n,n) ≤
(2n)^{π(2n)}`.  **DONE ∅-axiom**: `central_binom_ge_two_pow` (`2^n ≤ C(2n,n)`);
`floor_two_mul_div_le` (per-term `⌊2n/d⌋ ≤ 2⌊n/d⌋ + [d≤2n]`); **the Kummer bound
`vp_central_binom_le_floorLog : vp_p(C(2n,n)) ≤ ⌊log_p(2n)⌋`** (Legendre + per-term
sum, the hard analytic core); `prime_pow_vp_central_binom_le : p^{vp_p(C)} ≤ 2n`.
File under `Lens/` (layer guard blocks `Lib/Math` ← `MultSystemValue`); reuses
`Legendre`/`LcmGrowthChebyshev` (`Lib`) via `Lens → Lib`.  Bridge `fact_eq_factorial`.

**Next** (frontier): the single remaining gap is the **product bound `C(2n,n) ≤
(2n)^{π(2n)}`** — needs a *product-over-distinct-primes* (radical-support)
representation `m = ∏_{p≤N, prime} p^{vp_p m}` (FTA grouping), not yet built
(`factorization_exists` gives primes *with multiplicity*).  Then the cleared-form
final assembly `n ≤ π(2n)·⌊log₂(2n)⌋`.  Other follow-ups: PNT `~N/ln N` (constant
1) horizon; lcm-route cross-check.

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
