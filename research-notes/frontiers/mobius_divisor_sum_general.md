# Frontier: general Möbius divisor-sum `∀ n ≥ 1, Σ_{d∣n} μ(d) = [n=1]`

**Status**: PARTIAL (T2.5).  Prime case closed; general n open.

## Closed (∅-axiom, `lean/E213/Lib/Math/NumberTheory/MobiusPrimeCase.lean`)

- `mu_prime : Prime213 p → mu p = −1` (every prime).
- `mu_prime_sq : Prime213 p → mu (p·p) = 0` (every prime).
- `mobiusSum_prime : Prime213 p → mobiusSum p = 0` (every prime) — the **n = prime
  case** of the general identity.
- `muAux` branch toolkit: `muAux_{succ,zero,at_one,sq,strip,advance}`, and
  `muAux_skip` (scan past a run of non-divisors, consuming `gap` fuel).
- `sumZ_{succ,congr,const_zero,split_first}` Int divisor-sum toolkit.

## Open (T3 — general n) + precise obstruction

The corpus `mu` is `muAux`: **fuel-bounded trial division** scanning candidates
`d = 2, 3, 4, …` upward.  The identity `Σ_{d∣n} μ(d) = [n=1]` is about the
**squarefree / prime-factorization structure** of n.  Standard proofs need either
(a) `mu` multiplicativity `gcd(a,b)=1 → mu(ab)=mu a·mu b` + prime-power
`Σ_i μ(pⁱ)=0`, or (b) the binomial cancellation `Σ_{S⊆primes(n)}(−1)^|S|=0` over
squarefree divisors.

Three gates block T3:

1. **No structural prime-factor list / radical / squarefree-divisor set exists
   PURE.**  The corpus has `Prime213`, `vp`, `vp_mul`, `prime_dvd_mul` (Euclid),
   `coprime_mul_iff` — but no `primeFactors`, `radical`, `minFac`, or
   squarefree-divisor object.  Route (b) needs the prime set as an explicit finite
   structure to sum over.

2. **`mu` multiplicativity is the route-(a) bottleneck.**  Proving `mu(ab)=mu a·mu b`
   for coprime `a,b` from `muAux` requires showing the magnitude-ordered scan over
   `a·b` interleaves the prime factors of `a` and `b` and reproduces the two
   separate scans — a substantial invariant proof, NOT unlocked by `vp_mul` (which
   characterizes a *structural* valuation, not `muAux`'s scan state).

3. **Scan-start independence** (keystone for a `mu` recurrence): `muAux` strips `d`
   and recurses from `d+1`; equating that to `mu(m/d)` (restarts at 2) needs
   "`m/d` has no factor in `[2,d+1)`" carried as an invariant through the strong
   induction.

## Suggested attack

A PURE bridge `mu n = muStruct n`, where `muStruct` is defined from `vp`/`Prime213`
(squarefree test + parity of the distinct-prime count).  Then `vp_mul` +
`coprime_mul_iff` give `muStruct` multiplicativity directly, and a
`muAux`-correctness theorem (via `muAux_skip` + `muAux_strip` + scan-start
independence) transports it to the corpus `mu`.  `mu_prime`/`mu_prime_sq` are the
first two cases of exactly that correctness theorem.  This same `muStruct` bridge
would also unlock general σ/τ multiplicativity and Möbius inversion.
