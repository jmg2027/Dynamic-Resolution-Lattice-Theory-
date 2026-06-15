# Frontier: general Möbius divisor-sum `∀ n ≥ 1, Σ_{d∣n} μ(d) = [n=1]`

**Status**: ✅ **CLOSED for `muStruct`** (`MobiusDivisorSum.lean`):
`muStruct_divisor_sum (n) (0<n) : Σ_{d∣n} muStruct d = [n=1]`, general, ∅-axiom.
Also: divisor-product reindex closed (`DivisorMultiplicative.lean`) + general σ/τ
multiplicativity.  The **only remaining** open item is the `muStruct = mu` bridge
(to transport the divisor-sum from the structural `muStruct` to the corpus
trial-division `mu`) — the open `muAux`-correctness scan invariant (gates 2–3 below).
Möbius inversion `Σ_{d∣n} μ(d)·g(n/d)` is also now reachable from `divisorSumZ_product_reindex`.

## Update 4 — general Möbius divisor-sum CLOSED for `muStruct` (`MobiusDivisorSum.lean`)

`muStruct_divisor_sum (n) (0<n) : divisorSumZ n muStruct = (n == 1).toNat` — the
general `Σ_{d∣n} μ(d) = [n=1]` for the structural Möbius (41 PURE).  Pieces:
`divisorSumZ_product_reindex` (Int reindex), `muStruct_divisorSum_mul`
(multiplicative divisor-sum), `divisorSumZ_prime_pow_reindex` +
`muStruct_divisorSum_prime_pow` (= `sumMF k`, 0 for k≥1), `exists_prime_pow_cofactor`
(smallest-prime split).  Assembly: `n>1 ⇒ n = p^{k+1}·m ⇒ D(μ)(n) = 0·_ = 0`.

The remaining `muStruct = mu` bridge gates (unchanged, the ONLY thing left):

## Update 3 — the missing tool is BUILT; σ/τ multiplicativity CLOSED (`DivisorMultiplicative.lean`)

The sparse-fiber reindex is proven:
- ★★★ `divisor_product_reindex (a b) (gcd a b = 1) (0<a) (0<b) (f) :
  divisorSum (a·b) f = Σ_{i<a}Σ_{k<b} dvdInd i a · dvdInd k b · f((i+1)(k+1))`.
- ★★★ `sigma_mul` / `tau_mul` — σ, τ multiplicative over coprime products (general).

Built via a *double partition-by-key collapsing each cell to a single survivor*:
outer key `gcd(j+1,a)`, inner key `gcd(j+1,b)`; the divisor-factorization bijection
`j+1 = gcd(j+1,a)·gcd(j+1,b)` pins the unique survivor `j = e(k+1)−1` per cell
(`cell_pointwise`), each cell sum collapsing by `sum_eqInd_weight_eq`.  No
contiguous-block `sumTo_reshape` was needed.

**Remaining (general Möbius divisor-sum `Σ_{d∣n} μ(d) = [n=1]`)**: now directly
reachable — apply `divisor_product_reindex` (with `f = mu`/`muStruct`) to reduce to
the prime-power core `sumMF_succ_eq_zero` (`MobiusMultiplicative.lean`) via the
coprime split `n = p^k·m`.  That assembly + Möbius inversion `Σ_{d∣n} μ(d)·g(n/d)`
are the open follow-ons; the hard reindex tool is done.

## Update — structural multiplicativity CLOSED (`MobiusMultiplicative.lean`)

Both classical ingredients of the general identity are now PURE:
- `muStruct` — a structurally-defined Möbius (`∏_{q=2}^{n} mFactor(vp q n)` at
  primes, `1` at composites), verified `= mu` on n=1..12.
- ★★★ `muStruct_mul` — `gcd(a,b)=1 → muStruct(ab) = muStruct a · muStruct b`
  (general; the corpus's first structurally-defined multiplicative Möbius).
- ★★ `sumMF_succ_eq_zero` — prime-power core `Σ_i μ(pⁱ) = [k=0]`.

**Remaining gap for the general divisor-sum** is now purely combinatorial: the
coprime divisor-product factorization
`Σ_{d∣p^k·m} f = (Σ_i f(pⁱ))·(Σ_{d∣m} f)` over the `sumZ`/`dvdInd` representation —
needs a divisor-product reindex `divisors(p^k·m) ≅ {0..k}×divisors(m)` carried
through `sumZ` (the corpus has range-Fubini `sumTo_fubini` but no
Σ-over-divisors-Fubini for a *product* decomposition / no divisor-set object).
The same `muStruct_mul` window-product template would also unlock general σ/τ
multiplicativity + Möbius inversion.

## Update 2 — divisor-product infrastructure CLOSED, gap narrowed to ONE tool (`DivisorProductReindex.lean`)

The forward arithmetic of the divisor-product bijection is now fully PURE:
- ★★ `gcd_mul_coprime` — `gcd(a,b)=1 → gcd(d,a·b) = gcd(d,a)·gcd(d,b)` (corpus-absent
  gcd multiplicativity over coprime products).
- ★★ `divisor_factorization` — coprime `a,b`: every `d ∣ a·b` splits uniquely
  `d = gcd(d,a)·gcd(d,b)` (+ `divisor_factors_coprime` injectivity witness).
- `divisorSum_mul_as_grid` — the easy direction (grid double-sum = product of divisor-sums).
- ★ `weighted_partition_by_key` — reusable weighted disjoint-cover.
- ★★ `gcd_fiber_forward` — `e∣a, gcd(a,b)=1, d₂∣b ⟹ gcd(e·d₂,a)=e`.
- `sigma_mul_of_reindex` / `tau_mul_of_reindex` — conditional: reindex ⟹ σ/τ multiplicative.

**The gap is now exactly ONE general tool**: a *sum-reindex-by-bijection over `sumTo`
for a sparse (non-contiguous) fiber*.  Via `weighted_partition_by_key` (key
`j ↦ gcd(j+1,a)−1`) the reindex reduces to collapsing the class sum
`Σ_{j<ab} [gcd(j+1,a)=e]·dvdInd j (ab)·f(j+1)` to `Σ_{k<b} dvdInd k b·f(e·(k+1))` —
a reindex of `{d∣ab : gcd(d,a)=e} ↔ {d₂∣b}` via `d ↦ d/e`.  `sumTo_reshape` only
isolates *contiguous* blocks (as in `GaussTotient.gcd_class_count`); this fiber is
sparse.  Building that one permutation/bijection-sum lemma lands σ/τ multiplicativity,
the general Möbius divisor-sum, AND Möbius inversion together.

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
