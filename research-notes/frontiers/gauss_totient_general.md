# Frontier: general Gauss totient divisor-sum `Σ_{d∣n} φ(d) = n`

**Status**: OPEN.  T2 closed (def + table); T3 (general theorem) open.

## What is closed (∅-axiom, `lean/E213/Lib/Math/NumberTheory/EulerTotient.lean`)

- `totient n = Σ_{k=0}^{n-1} [gcd213 (k+1) n = 1]` — Euler's φ as a PURE count
  (`Bool.toNat` indicator, no `if`/propext).
- `divisorSum n f = Σ_{d∣n, 1≤d≤n} f d`, `gaussSum n = divisorSum n totient`.
- `gauss_totient_table` : `Σ_{d∣n} φ(d) = n` verified by `decide` for **n = 1..24**.
- `totient_table`, `totient_prime` (φ(p)=p−1 for small primes).

## What is open (T3 — the general theorem `∀ n ≥ 1, Σ_{d∣n} φ(d) = n`)

The standard proof partitions `{1,…,n}` by `g = gcd(k,n)`:
`count{k ≤ n : gcd(k,n) = g} = φ(n/g)` for each `g ∣ n`, then re-index the
divisor sum.  Two missing ∅-axiom ingredients:

1. **gcd-scaling bijection over a filtered count**:
   `count{k ≤ n : gcd(k,n) = g} = totient (n/g)`.
   The scaling fact `gcd213 (k·a) (k·b) = k·gcd213 a b` IS PURE (`Gcd213`), but
   lifting it to an equality of two filtered range-counts needs a
   count-preserving reindexing lemma the corpus lacks.

2. **disjoint-cover cardinality**:
   `sumTo n (fun _ => 1) = Σ_{g∣n} count{k ≤ n : gcd(k,n) = g}`
   (every `k` lands in exactly one gcd class).  Without `Finset.card` and its
   partition/bijection API this is a from-scratch counting build.

The existing reusable sum infra (`SumReshape.{sumTo_concat, sumTo_const,
sumTo_reshape}`, `Sum.sumTo_mod`) handles flat splits and grid reshapes but not
gcd-keyed partitioning of a count.

## Suggested attack

Build a small "filtered-count partition" toolkit:
`sumTo n f = Σ_{key} sumTo n (fun k => f k * [key k = key])` for a finite key
range — the gcd-class partition is then an instance.  This is the same shape the
inclusion-exclusion / derangement work needed; a reusable
`count_partition_by_key` lemma would unlock this AND future multiplicative-function
identities (σ, μ-inversion).
