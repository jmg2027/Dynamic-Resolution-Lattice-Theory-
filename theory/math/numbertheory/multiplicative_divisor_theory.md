# Multiplicative divisor theory (∅-axiom)

Mirror of `lean/E213/Lib/Math/NumberTheory/` (the divisor-function family).
Every theorem named here is PURE (`#print axioms → "does not depend on any
axioms"`); this chapter is the narrative, the Lean files are the source of
truth.

The residue, read under the **counting Lens** (sum/count over the divisors
`d ∣ n`), reproduces elementary multiplicative number theory end-to-end: the
arithmetic functions, their multiplicativity, the divisor-sum identities,
Möbius inversion, the Dirichlet convolution ring, and the classical parity /
perfect-number theorems — with no external axiom, no Mathlib, no `propext`.

## 1. The arithmetic functions

| function | meaning | Lean |
|---|---|---|
| `tau n` | number of divisors `Σ_{d∣n} 1` | `SumOfDivisors.tau` |
| `sigma n` | sum of divisors `Σ_{d∣n} d` | `SumOfDivisors.sigma` |
| `sigmaK k n` | `Σ_{d∣n} dᵏ` (`σ₀=τ`, `σ₁=σ`) | `GeneralizedDivisorSum.sigmaK` |
| `totient n` | Euler `φ` | `EulerTotient` |
| `mu n` | Möbius | `MobiusFunction.mu` |
| `liouville n` | Liouville `λ` | `LiouvilleFunction.liouville` |

All are defined by a propext-free `divisorSum`/trial-division core (`cond`/
`Bool.toNat` branching, no `ite`).

## 2. Multiplicativity

A function `f` is **multiplicative** when `gcd(m,n)=1 ⟹ f(mn)=f(m)f(n)`.
The unique prime factorization then reduces `f(n)` to its values on prime
powers. Proven ∅-axiom over coprime products:

- `DivisorMultiplicative.sigma_mul`, `tau_mul` — σ, τ multiplicative.
- `GeneralizedDivisorSum.sigmaK_mul` — σ_k multiplicative, **all k**.
- The engine is `DivisorProductReindex.divisor_product_reindex` /
  `DivisorMultiplicative.divisor_product_reindex` — the sparse-fiber grid
  reindex `divisorSum (a·b) f = Σ_{i<a}Σ_{k<b} dvdInd i a · dvdInd k b ·
  f((i+1)(k+1))`, the combinatorial heart of every multiplicativity proof.

## 2.5 The structural theorems (multiplicative functions as a family)

The per-function results above are instances of three theorems quantified
over *all* multiplicative `f` — the structure the whole family rests on:

- **Summatory** `SummatoryMultiplicative.summatory_mul`: `f` multiplicative
  ⟹ `g(n)=Σ_{d∣n} f(d)` multiplicative. `sigma_mul` (`f=id`) and `tau_mul`
  (`f≡1`) are one-line corollaries.
- **Convolution** `DirichletMultiplicative.dconv_mul`: `f,g` multiplicative ⟹
  `f∗g` multiplicative (the full `dconv` version; `summatory_mul` is the
  `g≡1` case). The multiplicative functions are closed under `∗`.
- **Uniqueness** `MultiplicativeUniqueness.mult_eq_of_prime_pow`: two
  multiplicative functions agreeing on every prime power are equal — a
  multiplicative function *is* determined by its prime-power values
  (the ×-count-Lens reading axis by axis).

All three close by the same smallest-prime-power strong induction
(`exists_prime_pow_cofactor`): split `n=p^k·m` (coprime, m<n), factor by
multiplicativity, recurse on `m`.

## 3. Divisor-sum identities (general n, not tables)

- **Gauss totient** `GaussTotient.gauss_totient`: `Σ_{d∣n} φ(d) = n`.
- **Möbius** `MobiusBridge.mu_divisor_sum`: `Σ_{d∣n} μ(d) = [n=1]`.
- **Liouville** `LiouvilleValuation.lambdaV_divisor_sum_isSquare`:
  `Σ_{d∣n} λ(d) = [n is a perfect square]` for **all n** — on the
  valuation-form `λV(n)=∏_p (−1)^{vp p n}`, a completely multiplicative
  function (`lambdaV_mul`, all m,n) reaching what the trial-division
  `LiouvilleFunction.liouville` gives only by table (the two agree for
  n≤16; the general bridge shares μ's open scan-correctness invariant).
- **Generalized** `GeneralizedDivisorSum.sigmaK` carries `σ_k` for all k.

## 4. Möbius inversion + the bridge to `mu`

- `MobiusInversion.mobius_inversion` — `g(n)=Σ_{d∣n} f(d) ⟹
  f(n)=Σ_{d∣n} μ(n/d)g(d)`; `divisor_pair_swap` is the Dirichlet-convolution
  commutativity core (`Σ_{d∣n}Σ_{e∣(n/d)} h = Σ_{e∣n}Σ_{d∣(n/e)} h`).
- `MobiusBridge` transports the whole framework from the structural
  `muStruct` to the corpus `mu` (`muStruct_eq_mu`, `mu_mul`, `mu_prime_pow`,
  `mu_mobius_inversion`).

## 5. The Dirichlet convolution ring

`DirichletConvolution.dconv f g n = Σ_{d∣n} f(d)·g(n/d)` makes arithmetic
functions `Nat→Int` a **commutative monoid with unit**:

- `dirichlet_comm`, `dirichlet_assoc` (commutativity + associativity).
- `DirichletIdentities`: `eps n = [n=1]` is the identity (`dconv_one_eps`,
  `dconv_eps_one`); `mu_conv_one` (`μ∗1=ε`), `phi_conv_one` (`φ∗1=id`),
  `sigma_eq_id_conv_one` (`σ=id∗1`).

The named identities are the multiplicative-structure restatements of §3.

## 6. Classical theorems closed on the framework

- **Euclid's perfect-number theorem** `PerfectNumbers.euclid_perfect`: if
  `q=2^(k+1)−1` is prime then `2^k·q` is perfect (`σ(N)=2N`), general k —
  via `sigma_mul` + `σ(2^k)=2^(k+1)−1` + `σ(q)=q+1`.
- **τ-parity** `TauParity.tau_odd_iff_square`: `τ(n)` odd ⟺ `n` is a perfect
  square. Proved by a symmetric **double-sum parity** core
  (`doubleSum_parity`: off-diagonal `d ↔ n/d` pairs cancel mod 2).
- **σ-parity** `SigmaParityComplete.sigma_odd_iff`: `σ(n)` odd ⟺ `n` is a
  square **or twice a square**. The capstone — assembled from
  `sigma_odd_iff_oddPart` (the 2-adic odd-part reduction,
  `OddPartDecomposition`), `sigma_odd_square_odd` (odd `m`: σ(m) odd ⟺ square,
  by smallest-prime-power strong induction), and `sq_or_twice_iff`
  (`SquareCharacterization`).

## 7. Square characterization (the σ-parity infrastructure)

`SquareCharacterization` + `OddPartDecomposition` build reusable squareness
infrastructure, all ∅-axiom:

- `decomp`: `n = 2^(v2 n)·oddPart n` (`oddPart` odd) — the 2-adic split.
- `coprime_isSquare_mul`: coprime `u,v ⟹ (IsSquare(uv) ↔ IsSquare u ∧
  IsSquare v)` — **general, via a pure-gcd route (no UFD)**: `u=gcd(u,r)²`
  from `uv=r²`.
- `isSquare_iff` (`IsSquare n ↔ v2 n even ∧ IsSquare(oddPart n)`),
  `sq_or_twice_iff` (`(n square ∨ n twice-square) ↔ IsSquare(oddPart n)`).
- `SquareValuation.isSquare_iff_all_vp_even`: the all-primes form —
  `IsSquare n ↔ ∀ p prime, vp p n even` (the general "square ⟺ every
  exponent even"; the 2-adic `isSquare_iff` is the `p=2` slice). By the
  same smallest-prime-power descent; `coprime_isSquare_mul` +
  `isSquare_prime_pow_iff`.

## 8. σ_m at a prime power, and divisor-sum multiplicativity for any completely-multiplicative weight

`SigmaPrimePowGeom` + `SigmaDivisorClosed` close the **general power-sum-of-divisors** `σ_m(n) =
Σ_{d∣n} dᵐ` (the `σ`/`τ` of §2 are `m=1`/`m=0`), all ∅-axiom:

- `sigma_prime_pow_divisor_geom`: `(pᵐ − 1)·σ_m(pᵏ) = p^{m(k+1)} − 1` — the genuine divisor sum
  over a prime power collapses (via the prime-power reindex `Σ_{d∣pᵏ} = Σ_{i≤k}` on `d=pⁱ`) onto
  the geometric series of ratio `pᵐ`, whose cleared closed form is the right-hand side.  Built on
  the cast-power bridge `↑(pⁱ) = (↑p)ⁱ` (`ofNat_pow_eq_ipow`) + `ipow_mul`.
- `divisorSumZ_mul_of_completely_mult`: **the reusable general law** — if `g(uv)=g(u)g(v)` for all
  `u,v`, then `divisorSumZ(ab) g = divisorSumZ a g · divisorSumZ b g` for coprime `a,b>0`.  This
  generalizes both `muStruct_divisorSum_mul` and the `σ`/`τ` multiplicativity of §2; `sigma_m_mul`
  (σ_m multiplicative) is a one-line corollary, since `d ↦ dᵐ` is completely multiplicative.

Closed form (§8.1) + multiplicativity (§8.2) together determine `σ_m` on every `n` from its
prime factorization, for every `m`.

## Promotion record

Promoted from the closed frontiers `gauss_totient_general`,
`mobius_divisor_sum_general`, `sigma_parity_general` (all ✅ closed;
archived under `research-notes/archive/numbertheory/`). The framework is
PURE end-to-end; this chapter is the permanent-tier narrative.  §8 (σ_m
closed form + general completely-multiplicative divisor-sum law) mirrors
the `SigmaPrimePowGeom` / `SigmaDivisorClosed` sub-tree.
