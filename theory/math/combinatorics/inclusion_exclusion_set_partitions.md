# Inclusion–exclusion and set-partition counting (∅-axiom)

Mirror of the `lean/E213/Lib/Math/Combinatorics/` inclusion–exclusion family.
Every theorem named here is PURE (`#print axioms → "does not depend on any
axioms"`); the Lean files are the source of truth.

The residue, read under the **finite-difference Lens** (the alternating
binomial transform `A n g = Σ_{k=0}^{n} (−1)^k C(n,k) g(k)`), reproduces the
algebraic core of the twelvefold way: binomial inversion, the surjection
count, derangements, and the surjection ↔ Stirling ↔ Bell chain — with no
external axiom, no Mathlib.

## 1. The signed binomial transform

`A n g = Σ_{k=0}^{n} (−1)^k C(n,k) g(k)` is the finite difference operator in
disguise: `SurjectionCount.A_rec` gives `A (n+1) g = A n (Δg)` with
`Δg k = g k − g(k+1)`, so `A n g = (Δⁿ g)(0)` (`A_eq_diffIt`). The degree
theory `PolyLe` records that `Δ^{d+1}` annihilates polynomials of degree ≤ d
— the engine behind every vanishing identity below.

## 2. Binomial inversion

`BinomialInversion`, over `Int`, via the signed binomial `sb n k =
(−1)^{n−k} C(n,k)` (signed Pascal `sb(n+1)(k+1) = sb n k − sb n(k+1)`):

- `binomial_orthogonality`: `Σ_{k=0}^{n} (−1)^{n−k} C(n,k) C(k,m) = [n=m]` —
  the inverse-pair relation, proved without the subset-of-subset identity
  (the signed-Pascal recurrence collapses it to `T(n+1,m+1)=T(n,m)`).
- `binomial_inversion`: `(∀n, g n = Σ_k C(n,k) f k) → (∀n, f n = Σ_k
  (−1)^{n−k} C(n,k) g k)` — the binomial transform is its own signed inverse.

## 3. The surjection count (inclusion–exclusion)

`SurjectionCount`: `surj m n = Σ_{k=0}^{n} (−1)^k C(n,k) (n−k)^m` (over `Int`)
counts surjections `[m] ↠ [n]`. The boundary identities are pure
finite-difference vanishing:

- `surj_zero_of_lt`: `m < n ⟹ surj m n = 0` (degree `m < n` is annihilated by
  `Δⁿ` — fewer elements cannot surject onto more).
- `surj_diag`: `surj n n = n!` (the `n!` bijections — the top difference of
  `xⁿ`).
- `surj_rec`: `surj(m+1)(n+1) = (n+1)·surj m (n+1) + (n+1)·surj m n`, via the
  absorption `(n+1−k)·C(n+1,k) = (n+1)·C(n,k)` (`choose_absorb_int`).

## 4. Derangements as inclusion–exclusion

`DerangementInclusionExclusion`: the corpus's recurrence-defined subfactorial
`derange` (!n) equals its closed form

- `derange_eq_inclusion_exclusion`: `!n = Σ_{k=0}^{n} (−1)^k C(n,k) (n−k)!`.

`dIE` is shown to obey the same `±1` one-term recurrence as `derange`; the
recurrence-match closes in one step (top term `(−1)^{n+1}`, head collapsing to
`(n+1)·dIE n` via the same `choose_absorb_int`).

## 5. Surjection ↔ Stirling ↔ Bell

The set-partition chain, all general:

- `StirlingExplicit.surj_eq_fact_mul_stirling`: `surj m n = n! · S(m,n)` —
  surjections `[m]↠[n]` are `n!` times the partitions of `[m]` into `n`
  blocks. Induction on `m` matching the Stirling recurrence
  `S(m+1,n)=n·S(m,n)+S(m,n−1)`; the `k·C(n,k)` reindex (`choose_succ_mul`) is
  the load-bearing step.
- `BellStirling.stirling2_succ_sum`: `S(n+1,k+1) = Σ_{j=0}^{n} C(n,j) S(j,k)`
  — the block-conditioning identity (the block containing element `n+1`).
- `BellStirling.bell_eq_stirling_sum_general`: `B_n = Σ_{k=0}^{n} S(n,k)` for
  **all** `n` (the corpus had only a `decide` table to `n≤5`). The row sum
  `bellS` satisfies the Bell recurrence `B_{n+1} = Σ_k C(n,k) B_k`
  (`bell_succ`) via the Fubini swap `sumTo_fubini` on the block-conditioning
  identity, so `bellS = bell` by induction.

## Methodology

The whole cluster is one move repeated: read a counting question through the
signed binomial transform `A`, then a *degree* or *recurrence* fact about the
weight `g` collapses the sum. `surj m n = 0` (m<n) is degree-vanishing;
`surj n n = n!` is the top difference; the Stirling/Bell links are
recurrence-matches. No `funext` is used anywhere (the proofs work pointwise
through `sumZ_congr`/`sumTo_congr`), keeping the cluster `Quot.sound`-free.
