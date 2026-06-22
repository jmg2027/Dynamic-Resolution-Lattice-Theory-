# Decomposition: the Riemann zeta function / the Euler product

*213-decomposition of `ζ(s) = Σ_n n^{-s} = Π_p (1−p^{-s})^{-1}`, per `../README.md`. LEVERAGE
attempt: does the Euler **product** FALL OUT of the unique-factorization character of
`prime_factorization.md`, or is it only a re-description of "ζ has two forms"?*

The hypothesis under test: the Euler product **IS** the prime-factorization character
(`prime_factorization.md`, the `×↦+` reading `L_vp` / unique factorization) **lifted to a
generating function**. The *additive* reading over all `n` (`Σ_n n^{-s}`) EQUALS the
*multiplicative* reading over primes (`Π_p (1−p^{-s})^{-1}`) precisely BECAUSE every `n` is
uniquely its prime-valuation vector (`eq_of_vp_eq`). So "ζ's two forms" is the *same* `⟨C|L⟩`
collapse as `prime_factorization.md`, now at the generating-function level — and the calculus
should *predict* the product from the UFD character, not merely relabel it.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **same `ℕ_{>0}` ×-construction** of `prime_factorization.md`:
  numbers built by multiplying distinguishable ×-atoms (primes) with multiplicity. Nothing new
  is constructed for ζ. The Euler product reads *exactly* the distinguishing-history `L_vp`
  reads — `n ↔ (v₂(n), v₃(n), v₅(n), …)`, faithfully (`FTAEquality.eq_of_vp_eq`,
  `PrimeValuation.vp_mul`). The single fact "every `n` is uniquely a finite prime-power product"
  is the entire content the product formula will cash.

- **Reading `L_ζ` — a *generating-function* reading: weight every member of the
  construction-family `{n : ℕ_{>0}}` by `n^{-s}` and sum.** `L_ζ = Σ_{n} a(n)·n^{-s}` for an
  arithmetic weight `a`. This is the **`weight`-reading of `probability.md`/`entropy.md` run over
  the whole construction-family at once** — the same move `fourier.md` made ("read through the
  *whole* dual"), here "weight the *whole* ×-construction by a multiplicative kernel and sum."
  The kernel `n ↦ n^{-s}` is itself **`exponential.md`'s `L_exp` character** (`+↦×` on the
  exponent, `vp_pow`): `n^{-s} = Π_p (p^{-s})^{v_p(n)}`, so the weight of `n` is the *product
  over primes of the per-axis weight raised to that axis's valuation*. The reading factors
  through the valuation vector because the kernel is multiplicative.

- **Residue** — for the *combinatorial/formal* identity (every `n` ↔ its unique prime-power
  product, the local factor a geometric series), **none** — exactly `prime_factorization.md`'s
  zero residue: the vector is faithful, so the bijection {`n`} ↔ {finite prime-power
  selections} is exact (`eq_of_vp_eq`). The residue surfaces one level up, at the *analytic*
  object: the **infinite sum/product and its convergence/value** is a `Real213` pointing — `ζ(s)`
  as a *number* is reached by no finite truncation, only by a narrowing modulus (the
  transcendental-cut residue, the `e`/`φ`-as-residue row of `exponential.md`). So the **formal
  Euler product is residue-free; the analytic ζ-value lives in the residue.**

## Re-seeing

```
   the kernel  n^{-s}            =  Π_p (p^{-s})^{v_p(n)}        ( L_exp, vp_pow: + ↦ × per axis )
   the ζ-reading L_ζ             =  Σ_{n∈ℕ_{>0}} a(n)·n^{-s}     ( weight the whole ×-construction & sum )
   "ζ has two forms"             =  Σ_n a(n) n^{-s} = Π_p (Σ_{k≥0} a(p^k) p^{-ks})
                                       FORCED by  n ↔ (v_p(n))_p  faithful  (eq_of_vp_eq)
   the local factor (a≡1)        =  Σ_{k≥0} p^{-ks} = (1−p^{-s})^{-1}   ( geometric series, geom_sum )
   "(p^m−1)·σ_m-style closed form" = (ipow p m −1)·Σ_{i≤k} p^{mi} = p^{m(k+1)}−1  (sigma_prime_pow_geom)
```

So the Euler product is *not* a second formula for ζ that an identity relates to the first. It is
the **single statement that `L_ζ` factors through the prime-valuation coordinates** — i.e. that
the weight is multiplicative (`vp_mul` lifted to the kernel) and the coordinate is faithful
(`eq_of_vp_eq`). The `Σ_n` = `Π_p` is the **distributive law of the faithful coordinate system**:
choosing one `n` = choosing, independently per prime axis, how many copies of that prime — and
"independently per axis" is `two_three_unique` (axes never trade) from `prime_factorization.md`.

## LEVERAGE — does the Euler product fall out of the UFD character? (prediction vs collapse — honest)

**Honest verdict: GENUINE prediction on the structural skeleton — the product *form* is derived,
not relabeled — with the analytic value an honestly-named open residue. Two of the three
load-bearing legs are ∅-axiom Lean theorems; the third (the analytic infinite-product limit) is
the `Real213`-cut residue this calculus already locates for every transcendental.**

What the calculus genuinely **predicts** (forcing, Lean-grounded):

1. **The product form is FORCED by faithful multiplicativity — `Σ_n = Π_p` is the distributive
   law of the valuation coordinate.** The calculus says: a `weight`-reading `Σ_n a(n)·(kernel)`
   over the ×-construction factors as `Π_p (local factor)` **iff** the integrand is multiplicative
   on coprime parts and the coordinate is faithful. Both are exactly `prime_factorization.md`'s
   content. Lean certifies the discrete heart of this at the level the repo computes with — the
   *summatory*/convolution form of "the sum factors over coprime parts":
   - `SummatoryMultiplicative.summatory_mul` (★★★): `f` multiplicative on coprime pairs ⟹
     `Σ_{d∣n} f(d)` is multiplicative — `divisorSum (a·b) f = divisorSum a f · divisorSum b f`
     for `gcd(a,b)=1`. This **is** the finite-`n` Euler-factorization: the sum over the
     construction splits into a product over coprime (⟹ per-prime) parts. Its engine is
     `DivisorMultiplicative.divisor_product_reindex` — the grid reindex `d ∣ a·b ↔ (d₁∣a, d₂∣b)`
     that is FTA made operational.
   - `DirichletMultiplicative.dconv_mul` (★★★): Dirichlet convolution of two multiplicatives is
     multiplicative. The Dirichlet ring is the *generating-function ring* of ζ; `dconv_mul` is
     the statement that the Euler-product structure is closed under the ring operation — the
     algebraic backbone of `ζ(s)·ζ(s−1) = Σσ(n)n^{-s}`-style identities.
   This is real prediction: from "the kernel is multiplicative + the coordinate is faithful," the
   product-over-primes form is *forced*, and Lean confirms the finite/coprime-split instance.

2. **The local factor is FORCED to be the geometric series `(1−p^{-s})^{-1}` — and it is the
   SAME `geom_sum` the repo already has.** Per prime axis, the weight runs over `k = 0,1,2,…`
   (how many copies of `p`), contributing `Σ_{k≥0} a(p^k)p^{-ks}`. For `a≡1` this is the
   geometric series `Σ_k p^{-ks} = (1−p^{-s})^{-1}`. The calculus *predicts* "one axis ⟹ one
   geometric factor" directly from `exponential.md`'s `L_exp` (`+↦×` on that axis, `vp_pow`), and
   Lean has the cleared finite form verbatim:
   - `GeometricSeries.geom_sum`: `(r−1)·Σ_{k≤n} rᵏ = r^{n+1} − 1` (∅-axiom).
   - `SigmaPrimePowGeom.sigma_prime_pow_geom` (★★): `(p^m−1)·Σ_{i≤k} p^{mi} = p^{m(k+1)}−1` — the
     **divisor-power-sum over a prime power as a geometric series with ratio `p^m`**. This is the
     Euler local factor `Σ_{i} (p^i)^{−s}` at integer/cleared resolution: the `(1−p^{-s})^{-1}`
     factor is *literally* `geom_sum` read at `r = p^{−s}`, and the repo computes the integer
     dual exactly. The local factor is **predicted and Lean-certified** (at the algebraic
     resolution; the `s`-complex version is the residue, leg 3).

3. **The analytic ζ-value (the infinite sum, the infinite product, their convergence and equality
   *as numbers*) is the `Real213`-cut RESIDUE — honestly open, exactly as `e`/`φ` are.** There is
   **no `ζ(s)` analytic object in Lean** (grep `zeta`/`Zeta` in `NumberTheory/` returns only
   `Zeta3Numerator` = the *cleared integer numerator* of the ζ(3)/Apéry recurrence, NOT ζ as a
   function, and `LcmGrowthChebyshev`/`ChebyshevLower` = the PNT-direction prime-density bounds).
   The infinite product `Π_p` and infinite sum `Σ_n` *as values* sit in the transcendental-cut
   residue this calculus assigns to every irrational real (`exponential.md`'s `e`,
   `the_form_of_the_residue.md`). The calculus's own rule applies: **the value is the residue,
   reached by no truncation — the operand is the finite modulus.** The repo's closest computable
   handle on a ζ-flavored constant is the PNT density:
   - `Lens/Number/Nat213/ChebyshevLower.chebyshev_constant_interval` — a **computable narrowing
     interval** for the Chebyshev/PNT constant (sharpening with `m`, the modulus-as-operand rule),
     and `chebyshev_lower`/`chebyshev_order` the `π(N) ≍ N/log N` band.
   - `NumberTheory/FactorialLcmIdentity.vp_factorial_eq_sum_vp_lcm`: Legendre-as-Fubini, the
     additive-count = multiplicative-prime bridge that is the *combinatorial shadow* of the same
     `Σ↔Π` reindex (`exponential.md` already cites this for `e`'s discrete generator). And
     `Primorial.primorial_le_four_pow` (★★★★★) `Π_{p≤N} p ≤ 4ᴺ` — a genuine finite Euler product
     over primes, bounded.

   So leg 3 is **not a hand-wave gap but a located residue**: ζ-as-a-number is a pointing, and the
   product-equals-sum statement *as a numerical identity* requires the `Real213` infinite-product
   limit the repo has not built — declared open, consistent with the calculus's transcendental
   rule.

**Net:** the Euler product **falls out** of the UFD character as a *form* — `Σ_n = Π_p` IS the
faithful-coordinate distributive law (`summatory_mul`/`dconv_mul`, the FTA grid reindex
`divisor_product_reindex`), and the local factor IS the geometric series (`geom_sum`,
`sigma_prime_pow_geom`), both ∅-axiom. This is **prediction, not collapse-only**: the product
shape and the `(1−p^{-s})^{-1}` factor are *derived* from "multiplicative kernel + faithful
valuation," not relabeled. The honest boundary is identical to `fourier.md`/`exponential.md`: the
**analytic ζ-value / infinite-product convergence is a `Real213`-cut residue**, located not
waved.

## Note for the technique — is "a generating function = a reading summed/producted over a whole construction-family" a new construct?

**Yes — and it is the dual move to `fourier.md`'s "read through the whole dual," now in the
`weight`/`character` direction. Record it as a first-class reading-shape.**

`probability.md` gave `L` a **weight** slot; `entropy.md` made the weight *compose in series*
with a character; `fourier.md` promoted the reading to run over the **whole dual `Ĉ`** at once.
A **generating function** is the third member of this "read over a whole family" pattern:

> **Add the *generating reading* `L_gen = Σ_{x∈family} a(x)·(kernel)^{f(x)}` — a `weight`-reading
> applied to an *entire construction-family*, the kernel being a `character` (`L_exp`).** When the
> family is the ×-construction and the kernel is multiplicative, `L_gen` **factors over the atoms**
> (primes) — the **Euler product is the factorization of a generating reading through the faithful
> valuation coordinate**. The product-over-primes is the `prime_factorization.md` `Σ↔Π` collapse
> *summed over the whole family*, exactly as `fourier.md`'s transform is the character collapse
> *summed over the whole dual*. So: **Fourier = sum over the dual `Ĉ`; the Dirichlet/Euler
> generating function = sum over the construction `C` itself, weighted by a multiplicative
> kernel.** Two faces of "read the whole family at once," one in each direction of the character
> arrow.

This **confirms the `×↦+` character lifts to generating functions** — and sharpens *how*: the lift
is not the character acting on one element but the character's *multiplicativity* propagating
through a `Σ`-over-the-family into a `Π`-over-the-atoms. The faithful valuation coordinate
(`eq_of_vp_eq`) is what makes the `Σ↔Π` an *equality* rather than a one-way bound; `two_three_unique`
(axes never trade) is what makes the per-prime factors *independent* (a true product, not a
correlated one). So the Euler product sits exactly where `prime_factorization.md`'s three legs meet
— homomorphism (`vp_mul`/`summatory_mul`), faithfulness (`eq_of_vp_eq`), axis-independence
(`two_three_unique`) — lifted one level to the generating-function family. The deepest collapse: ζ's
"two forms," the Dirichlet ring's multiplicativity, and the per-prime geometric factor are **one
reading** — the generating reading factored through the UFD coordinate — and the analytic ζ-value is
its residue.

## Verified Lean anchors (grep-verified to exist)

- `Lib/Math/NumberTheory/FTAEquality.lean:eq_of_vp_eq` — the faithful valuation coordinate (equal
  `vp` at every prime ⟹ equal) = the `Σ↔Π` bijection's exactness.
- `Lib/Math/NumberTheory/PrimeValuation.lean:vp_mul` — the `×↦+` character homomorphism.
- `Lib/Math/NumberTheory/SummatoryMultiplicative.lean:summatory_mul` (★★★) — sum over the
  construction factors over coprime parts (the finite-`n` Euler factorization); corollaries
  `sigma_mul`, `tau_mul`.
- `Lib/Math/NumberTheory/DivisorMultiplicative.lean:divisor_product_reindex` — the FTA grid
  reindex `d∣a·b ↔ (d₁∣a, d₂∣b)` powering the factorization.
- `Lib/Math/NumberTheory/DirichletMultiplicative.lean:dconv_mul` (★★★) — Dirichlet convolution
  preserves multiplicativity (the generating-function ring closed under the Euler structure).
- `Lib/Math/NumberTheory/GeometricSeries.lean:geom_sum` — `(r−1)·Σ_{k≤n} rᵏ = r^{n+1}−1`, the
  local factor `(1−p^{-s})^{-1}` at cleared resolution.
- `Lib/Math/NumberTheory/SigmaPrimePowGeom.lean:sigma_prime_pow_geom` (★★) — the prime-power
  divisor-power-sum as a geometric series with ratio `p^m` (the Euler local factor, integer dual).
- `Lib/Math/NumberTheory/PrimeValuation`/`Meta/Nat/VpMul.vp_pow`, `vp_self_pow` — the kernel
  `n^{-s} = Π_p (p^{-s})^{v_p(n)}` per-axis scaling (`exponential.md`'s `L_exp`).
- `Lib/Math/NumberTheory/FactorialLcmIdentity.lean:vp_factorial_eq_sum_vp_lcm` — Legendre-as-Fubini,
  the additive-count = multiplicative-prime bridge (the `Σ↔Π` reindex's combinatorial shadow).
- `Lib/Math/NumberTheory/Primorial.lean:primorial_le_four_pow` (★★★★★) — `Π_{p≤N} p ≤ 4ᴺ`, a
  genuine finite Euler product over primes.
- `Lens/Number/Nat213/ChebyshevLower.lean:chebyshev_constant_interval`, `chebyshev_lower`,
  `chebyshev_order` — the PNT-direction prime-density band; the constant as a computable narrowing
  interval (the residue-as-modulus rule applied to a ζ-flavored constant).

## Conceptual-only legs (honest — ζ-analytic is THIN)

- **ζ(s) as an analytic function / the infinite sum `Σ_n n^{-s}` and infinite product `Π_p` as
  values, and their convergence/equality as numbers** — NO Lean object (grep `zeta`/`Zeta` in
  `NumberTheory/` returns only `Zeta3Numerator` = the cleared *integer numerator* of the Apéry/ζ(3)
  recurrence, not ζ-as-a-function). This is the `Real213`-cut residue, located by the calculus's
  transcendental rule, not built.
- **The Euler product as a stated *theorem* `Σ_n n^{-s} = Π_p (1−p^{-s})^{-1}`** — absent as a
  single Lean statement; certified only via its *finite/coprime-split* shadow (`summatory_mul`,
  `dconv_mul`, `divisor_product_reindex`) and its *local factor* (`geom_sum`,
  `sigma_prime_pow_geom`). The structural prediction is closed; the analytic assembly is open.
- **Analytic continuation, functional equation, non-trivial zeros** — entirely conceptual; far
  outside any present Lean. Not claimed.
