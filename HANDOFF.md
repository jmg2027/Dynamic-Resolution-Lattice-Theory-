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

### `E213/Lens/Number/Nat213/MultSystemValue.lean` (14 PURE)
The prime-valued instance — abstract monomials ARE distinct naturals.
  - `expVal` + `expVal_inj` / `caseA_distinct_naturals` : `C(N+k,k)` degree-≤N
    monomials over k primes are `C(N+k,k)` DISTINCT naturals (unique
    factorization, `vp_separation`).
  - `factorization_exists` (`fromVec`): every n>0 = product of primes.
  - `vp_pow_le_self` : `p^(vp p n) ≤ n` (per-axis exp/log).
  - `omega_le_log` : `2^(Ω n) ≤ n`, i.e. `Ω(n) ≤ log₂ n` (total exp/log skeleton).
  - `factorization_bounded` : prime factors of n are ≤ n ⇒ naturals ≤ N use only
    primes ≤ N, so `k = π(N)` bases suffice.

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
Targets: lower bounds on `π` (e.g. `2 ≤ primePi n` for `n ≥ 3`, infinitude /
growth); a Chebyshev-type *finite* bound pointing at PNT; tie
`factorization_bounded`'s prime list length to `primePi`.  PNT `π(N) ~ N/ln N` =
asymptotic horizon (pointing), not a ∅-axiom target.

## Propext-avoidance learned this branch (IMPORTANT)
Carry **propext**: `Nat.mul_assoc`, `Nat.dvd_trans`, `Nat.le_of_dvd`,
`Nat.decidable_dvd`, `Bool` `_eq_true` reflection.  Pure: `Nat.add_assoc`,
`Nat.mul_comm`, `Nat.le_antisymm`, `Nat.lt_or_ge`, `searchDiv`.  Use
`NatHelper.mul_assoc`/`mul_left_comm`, `Pow213.le_of_dvd_pos`, `decDvd`.  Note: a
Prop `∨` cannot eliminate into a `Decidable`/Type goal — branch on Nat values or
decidable instances, not Prop disjunctions.
