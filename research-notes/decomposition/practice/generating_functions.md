# Decomposition: generating functions / formal power series

*213-decomposition of `Σ aₙ xⁿ` (OGF/EGF, the Cauchy product, the Euler product, recurrences ↔
rational GFs), per `../README.md`. LEVERAGE attempt: does the calculus PREDICT the Cauchy-product
structure of generating functions — i.e. that **multiplication of generating functions = convolution
= the `⋆` just built in `Probability/Limit/ConvolveProfile`** — and UNIFY `zeta_euler.md` (Euler/
Dirichlet), `ConvolveProfile` (Cauchy product), and recurrences (`golden_ratio.md`) under one
"read-the-family-at-once" reading?*

The hypothesis under test: a **generating function `Σ aₙ xⁿ` is the family-reading** — `fourier.md`'s
and `zeta_euler.md`'s "read the whole construction-family `C` as one object," the `x`-slot being the
**bookkeeping resolution variable** (which member of the family a coefficient sits at). The OGF bundles
the bare count-reading; the EGF weights by `1/n!`. And the **product of two generating functions is the
Cauchy convolution** `(f·g)ₙ = Σ_{i+j=n} fᵢ·gⱼ` — which is *literally* the `⋆` operator
`ConvolveProfile.conv` just built, with the two characters on it (`mass` multiplicative, `momentNum`
additive) being the `×↦·` / `×↦+` arrow read on one convolution.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **counted construction-family** `{Cₙ}_{n∈ℕ}`: for each `n`, the (finite)
  number `aₙ` of distinguishables of "size `n`" (lattice paths of length `n`, partitions of `n`, the
  binomial row `n`, the prime-power tower at axis `p`, …). This is exactly `cardinality.md`'s
  count-reading applied family-wide, indexed by a **fold-height / size axis** `n` (`dimension.md`'s
  height). Nothing new is constructed: `C` is the same distinguishing, stratified by size. (Lean
  shadow: a coefficient sequence `CoeffSeq := Nat → Nat`, `GeneratingFunction.lean:27` — the family's
  size-indexed counts, *as a function object*, exactly the way `ConvolveProfile.Profile := List Nat`
  packages a finite weight `f[k]` at position `k`.)

- **Reading `L_gen` — the *generating reading*: bundle the whole size-indexed count-family into one
  object, the `x`-slot being the bookkeeping resolution variable.** `L_gen = Σ_n aₙ xⁿ`. The `xⁿ`
  is **not a number being raised to a power** — it is a *positional tag*, the resolution coordinate
  "this coefficient lives at size `n`" (`GeneratingFunction.xVar = fun n => if n=1 then 1 else 0`,
  `:36` — `x` is *the indicator at position 1*, the unit shift, not a scalar). So `L_gen` is the
  **`weight`-reading of `probability.md` run over the entire family at once**, where the "weight" of
  the size-`n` slab is the count `aₙ` and the carrier `xⁿ` records *where*. This is the same "read the
  whole family" move `fourier.md` made (sum over the dual `Ĉ`) and `zeta_euler.md` made (sum over `C`
  weighted by `n^{-s}`) — here in its **bare combinatorial direction**: the OGF is the count-reading
  bundled (kernel `xⁿ`, every member weighted `1`); the **EGF** is the *same* family-reading with the
  weight `1/n!` (the resolution kernel divided by the size-`n` symmetry group, an `exponential.md`
  `L_exp`-flavoured per-size normalization).

- **Residue** — for the **formal/combinatorial** object (a coefficient sequence, the product a finite
  Cauchy sum), **none** — exactly `ConvolveProfile`'s and `zeta_euler.md`'s zero residue: each
  coefficient `(f⋆g)ₙ = Σ_{i+j=n} fᵢ gⱼ` is a *finite* `Nat`-sum, computed exactly
  (`conv` is one-row recursion on `List Nat`, pure `Nat`, no analysis). The residue surfaces one level
  up, at the **analytic** object: the GF *as a function of a numeric `x`* (its radius of convergence,
  its value, the closed form `x/(1−x−x²)` *as a real function*) is a `Real213` pointing — reached by
  no finite truncation, the same transcendental-cut residue `zeta_euler.md`/`exponential.md` assign to
  every infinite series. The repo's own GF files state this paradigm verbatim: *"213 substrate truncates
  exactly … generating functions are finite polynomials, not infinite series"*
  (`GeneratingFunction.lean:9-16`; `Complex/PowerSeries.lean:6-18`). So the **formal GF is residue-free;
  the analytic GF-as-a-function lives in the residue.**

## Re-seeing — ⟨C | L_gen⟩

```
   a coefficient seq aₙ      =  ⟨ size-indexed count-family {Cₙ} | count-reading ⟩   (C; cardinality.md, height-indexed)
   the OGF  Σ aₙ xⁿ          =  ⟨ {Cₙ} | L_gen ⟩  (weight the whole family, kernel xⁿ = positional tag)
   the variable x            =  the bookkeeping resolution coordinate  (xVar = indicator at position 1, NOT a scalar)
   the EGF  Σ (aₙ/n!) xⁿ     =  the SAME L_gen with per-size weight 1/n!   (exponential.md's L_exp normalization)
   PRODUCT  (f·g)ₙ           =  Σ_{i+j=n} fᵢ·gⱼ   =  the Cauchy convolution  =  ConvolveProfile.conv (f ⋆ g)
   "GF mult = convolution"   =  mass_conv / momentNum_conv  (the two characters on ONE convolution)
   Euler product Σ_n = Π_p   =  L_gen over the ×-construction, factored through the UFD coordinate (zeta_euler.md)
   Fibonacci GF  x/(1−x−x²)  =  the q=+1 self-applying recurrence (golden_ratio.md) read as a power series
```

So a generating function is **not** a new kind of object. It is the **family-reading**: `cardinality.md`'s
count-reading applied to a *height-stratified* construction-family and bundled into one carrier, with the
`x`-slot doing exactly what `derivative.md`'s resolution parameter does — recording *which size* a
coefficient sits at. The three classically-separate "GF facts" collapse to one reading read three ways:

1. **The Cauchy product IS the convolution `⋆`** — and this is now Lean-grounded. The product of two
   generating functions, coefficient-by-coefficient, is `(f·g)ₙ = Σ_{i+j=n} fᵢ gⱼ` — *defined twice
   in-repo, identically*: `GeneratingFunction.convolution` (`:50`) and `ConvolveProfile.conv`/`⋆`
   (`:149`, the one-row recursion `conv (a::f) g = addL (scale a g) (0 :: conv f g)`). The decisive
   addition `ConvolveProfile` makes over the combinatorial file is the **proven characters on the
   product**: `mass (f⋆g) = mass f · mass g` (`mass_conv`, ∅-axiom) — *total mass is multiplicative
   under GF multiplication* — and `momentNum (f⋆g) = momentNum f·mass g + mass f·momentNum g`
   (`momentNum_conv`, ∅-axiom) — *the mean is additive*. These are the **`×↦·` and `×↦+` characters of
   the calculus read on one convolution**: `mass` (the GF evaluated at `x=1`, the total count) is the
   *multiplicative* character (the same arrow as `vp_mul`/`det2_mul`/`Independence.joint`); `momentNum`
   (the `x·d/dx` first moment) is the *additive* character (the same arrow as
   `Expectation.discreteNum_append`). **One convolution, two characters — exactly the `probability.md`
   structure.**

2. **The Euler product is `L_gen` over the ×-construction** — `zeta_euler.md` is the *same family-reading*
   with the kernel `n^{-s}` multiplicative, so `L_gen` factors through the faithful prime-valuation
   coordinate (`eq_of_vp_eq`) into `Π_p (local geometric factor)`. The Dirichlet ring is the
   *generating-function ring* of that family; `dconv_mul` is its product closed under multiplicativity.
   So `zeta_euler.md`'s `Σ_n = Π_p` and this file's Cauchy product are **two products on two indexings
   of one family-reading** — Dirichlet (multiply the index, `aₘₙ` for coprime `m,n`) vs Cauchy (add the
   index, `Σ_{i+j=n}`). The convolution `⋆` is the *additive-index* product; the Dirichlet convolution
   is the *multiplicative-index* one — both the "product = convolution" law, indexed by the two
   monoid structures on `ℕ` (`+` and `×`).

3. **Recurrences ↔ rational generating functions** — a linear recurrence is the `q=±1` self-applying
   residue of `golden_ratio.md` read as a power series. The Fibonacci recurrence `fib(n+2) = fib(n+1) +
   fib(n)` (`FibonacciAtomicLock.lean:34`, the literal `fib` definition) has GF `x/(1−x−x²)`, whose
   denominator `1−x−x²` *is the recurrence's characteristic relation written in the `x`-slot* — and its
   reciprocal `1/(1−x−x²)` is the geometric-series-style residue of the self-applying iterator `T(p,q) =
   (2p+q, p+q)` (`mobius_iteration_master`, `:119`). The rational GF is the **closed form of a `q=+1`
   converging residue** (`cassini_law_one_at_two_multipliers`, `:163`): a recurrence = a denominator,
   the roots of the denominator = the residue's fixed points (φ and its conjugate), the GF's partial
   fractions = the closed-form `aₙ = c₁φⁿ + c₂ψⁿ`. So "linear recurrence ↔ rational GF" is **the
   `golden_ratio.md` residue, bundled by `L_gen`** — the recurrence is the finite signature, the
   rational function its family-reading carrier.

## LEVERAGE — does the calculus PREDICT the Cauchy product, and UNIFY the three? (honest)

**Honest verdict: PREDICTION on the structural skeleton, now sharper than `zeta_euler.md`/`fourier.md`
because the load-bearing leg is FULLY Lean-grounded, ∅-axiom.** The calculus predicts that the
family-reading `L_gen`, once you can *multiply* two families, must multiply them *by convolution* (the
only product compatible with the size/height grading `xⁱ·xʲ = x^{i+j}`), and that the readouts of that
product split into a multiplicative character (total count) and an additive one (mean/degree). Both
predictions are **machine-checked, ∅-axiom**, in `ConvolveProfile` — built independently for the CLT,
yet *exactly* the GF product structure. This is the strongest form of the technique's bar: the
convolution and its two characters were proved for *probability*, and the GF decomposition shows they
*are* the generating-function product — a genuine collapse, not a re-skin.

What the calculus genuinely **predicts**, Lean-grounded:

1. **GF multiplication = convolution, and the product's readouts are the two characters — FORCED and
   PROVEN ∅-axiom.** The grading `x`-slot forces the product to be the Cauchy convolution (the unique
   product respecting `xⁱ·xʲ = x^{i+j}`). `ConvolveProfile.conv`/`⋆` *is* that convolution
   (`GeneratingFunction.convolution` defines the same sum). The calculus predicts the total-count
   readout must be a `×↦·` homomorphism and the mean a `×↦+` one — and both are theorems:
   - `ConvolveProfile.mass_conv` (★★★): `mass (f⋆g) = mass f · mass g` — **∅-axiom, verified by
     `#print axioms`** ("does not depend on any axioms"). GF-product is multiplicative on the total
     count `Σ aₙ` (the GF at `x=1`): the multiplicative character on the convolution.
   - `ConvolveProfile.momentNum_conv` (★★★): `momentNum (f⋆g) = momentNum f·mass g + mass f·momentNum g`
     — **∅-axiom**. The first moment (degree/mean) is *additive* under the product: the additive
     character. `μ(f⋆g) = μ(f)+μ(g)`.
   - `ConvolveProfile.profileMean_conv`, `mass_Phi_profile`, `momentNum_Phi_profile` — **∅-axiom** —
     the self-convolution doubling map's closed-form readouts (mass squares, mean doubles).
   This is real prediction *fully cashed*: "the family-reading's product is convolution, with a
   multiplicative total-character and an additive moment-character," and Lean confirms every clause
   ∅-axiom. The honest boundary `fourier.md`/`zeta_euler.md` had to name as open (the analytic value)
   is *not load-bearing here* — the product law itself is the prediction, and it is closed.

2. **The Cauchy product exists in the combinatorics tree too, and the `x`-variable is the positional
   tag — PARTIALLY built.** `GeneratingFunction.lean` (∅-axiom: `conv_one_at_0`, `catalanGF_table`,
   `xVar_at_1` all verified clean) builds `CoeffSeq := Nat → Nat`, the unit series `one`, the variable
   `xVar` (*as the position-1 indicator*, confirming the "`x` = bookkeeping coordinate" reading), and
   `convolution` (the Cauchy product). So the formal GF *object* is real and PURE. **But it proves only
   `(1·f)₀ = f₀`** (`conv_one_at_0`) — it does NOT prove the product is associative/commutative, nor a
   multiplicativity homomorphism on any readout. The *proven* product law lives in `ConvolveProfile`
   (`mass_conv`/`momentNum_conv`); the two files build the same `Σ_{i+j=n}` but are **not welded**.

3. **The Euler/Dirichlet face and the recurrence face are the same `L_gen`, other indexings — Lean
   anchors prior, verified.** `zeta_euler.md`'s `summatory_mul` (★★★, ∅-axiom verified), `dconv_mul`
   (★★★), `geom_sum` (∅-axiom verified), `divisor_product_reindex` (★★★) give the multiplicative-index
   product; `golden_ratio.md`'s `mobius_iteration_master` (∅-axiom verified), `fib`,
   `cassini_law_one_at_two_multipliers`, `cfQn_fib` give the recurrence/rational-GF residue. The GF
   reading is what **unifies** them: Cauchy product (additive index, `ConvolveProfile`), Dirichlet
   product (multiplicative index, `zeta_euler.md`), rational GF (the `q=±1` recurrence residue,
   `golden_ratio.md`) are three products / closed-forms on one family-reading.

**Net:** generating functions = the **family-reading** `L_gen`, whose **product is the convolution `⋆`**
— and unlike `fourier.md`/`zeta_euler.md`, the load-bearing prediction (product = convolution, with the
two characters) is **FULLY ∅-axiom Lean-grounded** via `ConvolveProfile.mass_conv`/`momentNum_conv`
(built for the CLT, *are* the GF product). The decomposition **consolidates** `zeta_euler.md` +
`ConvolveProfile` + recurrences under "read the family at once": Cauchy product, Euler/Dirichlet product,
and rational-GF recurrences are three indexings/closed-forms of one reading. **PREDICTION** — the
sharpest GF-class entry, because the product structure (not just the form) is a verified theorem.

## Revelation (collapse + forcing)

**The single deepest collapse:** the **convolution `⋆` built for the Central Limit Theorem IS the
generating-function product** — and the calculus *predicted* it must be, because the family-reading's
grading `x`-slot forces multiplication to be convolution. `ConvolveProfile.mass_conv` ("convolving two
distributions of total mass `M,N` gives mass `M·N`") and the schoolbook fact "the GF of a sum of
independent variables is the product of their GFs" are **literally one ∅-axiom theorem read in two
fields**. The two characters on that one convolution — `mass` multiplicative, `momentNum` additive — are
the calculus's two load-bearing invariants (`×↦·`, `×↦+`) appearing *together on a single operator*, the
cleanest joint sighting in the notebook. And the `x`-variable, long suspected to be "the missing formal
ring," turns out to be **the bookkeeping resolution coordinate** (`xVar` = the position indicator,
`derivative.md`'s resolution axis used as a *grading*), not a numeric scalar — dissolving the "where is
the power-series ring?" worry into "the family-reading's height-index, already carried."

Three "different" products collapse to one family-reading at different index monoids:
- **Cauchy product** (additive index `i+j=n`): `ConvolveProfile.conv` / `GeneratingFunction.convolution`.
- **Dirichlet product** (multiplicative index `mn`): `zeta_euler.md`'s `dconv_mul`/`summatory_mul`.
- **Rational GF / recurrence** (the denominator = the `q=±1` characteristic relation): `golden_ratio.md`.

So "GF multiplication = convolution," "ζ's two forms," and "recurrence ↔ rational function" are **one
reading** — `L_gen`, the family bundled — read at the two `ℕ`-monoids and at the recurrence residue. The
forcing: *given* the family-reading and a grading `x`, the product *must* be convolution (only product
respecting `xⁱxʲ=x^{i+j}`), and `mass_conv`/`momentNum_conv` prove the readouts split into the two
characters — not assumed, derived and ∅-axiom-verified.

## Note for the technique — `L_gen` is the family-reading; its PRODUCT is the calculus's convolution

**Record `L_gen` (the generating reading) as the family-bundling shape whose product is `⋆`, completing
the "read the whole family" trio.** `fourier.md` read the family over the dual `Ĉ`; `zeta_euler.md` read
it over `C` with a multiplicative kernel; **generating functions read it over `C` with a positional
(grading) kernel `xⁿ`** — and the new content is the *product*:

> **A generating function `Σ aₙ xⁿ` is `L_gen`: the count-reading of a height-indexed family,
> bundled, the `x`-slot the resolution/grading coordinate. Its product is the Cauchy convolution
> `⋆` (`ConvolveProfile.conv`), with `mass` the multiplicative `×↦·` character and `momentNum` the
> additive `×↦+` character — the two invariants on one operator. The Euler/Dirichlet GF is `L_gen` at
> the multiplicative index (`zeta_euler.md`); the rational GF is `L_gen` of the `q=±1` recurrence
> residue (`golden_ratio.md`). Three indexings / closed-forms, one reading.**

No new axis: this is `probability.md`'s `weight` + `derivative.md`'s `resolution` (used as grading) +
the `×↦·`/`×↦+` character — assembled into the family-reading. The OGF is `weight=1`; the EGF is
`weight=1/n!` (an `exponential.md` per-size normalization). The deepest open Lean target the calculus
*predicts*: **weld `GeneratingFunction.convolution` to `ConvolveProfile.conv` and lift `mass_conv` to a
general formal-power-series multiplicativity homomorphism** — a `CoeffSeq` (or `Profile`) commutative
semiring with `xVar` the grading generator, on which the GF product is associative/commutative and the
two characters are ring homomorphisms. That is the precise missing leg (below).

## Verified Lean anchors (grep- and `#print axioms`-verified)

| Leg | Theorem (file:line) | Purity |
|---|---|---|
| ★★★ GF product = convolution: total mass multiplicative | `Lib/Math/Probability/Limit/ConvolveProfile.lean:190` `mass_conv` (`mass (f⋆g)=mass f·mass g`) | ∅-axiom ✓ (`#print axioms`: no axioms) |
| ★★★ GF product: first moment / mean additive | `…/ConvolveProfile.lean:239` `momentNum_conv` (`momentNum(f⋆g)=momentNum f·mass g + mass f·momentNum g`) | ∅-axiom ✓ (`#print axioms`) |
| convolution operator `⋆` + Profile type | `…/ConvolveProfile.lean:115` `Profile := List Nat`, `:149` `conv`, `:154` `infixl ⋆` | def |
| self-convolution doubling readouts | `…/ConvolveProfile.lean:268` `profileMean_conv`, `:282` `mass_Phi_profile`, `:288` `momentNum_Phi_profile` | ∅-axiom ✓ (`#print axioms`) |
| formal GF object: CoeffSeq, x-variable, Cauchy product | `Lib/Math/Combinatorics/GeneratingFunction.lean:27` `CoeffSeq`, `:36` `xVar`, `:50` `convolution`, `:58` `conv_one_at_0`, `:80` `catalanGF_table` | ∅-axiom ✓ (`#print axioms` on `conv_one_at_0`, `catalanGF_table`, `xVar_at_1`) |
| Euler/Dirichlet face (multiplicative index) | `Lib/Math/NumberTheory/SummatoryMultiplicative.lean:74` `summatory_mul`; `DirichletMultiplicative.lean:132` `dconv_mul`; `DivisorMultiplicative.lean:289` `divisor_product_reindex` | `summatory_mul` ∅-axiom ✓ (`#print axioms`); others prior (`zeta_euler.md`) |
| local geometric factor | `Lib/Math/NumberTheory/GeometricSeries.lean:30` `geom_sum`; `SigmaPrimePowGeom.lean:26` `sigma_prime_pow_geom`; `Primorial.lean:102` `primorial_le_four_pow` | `geom_sum` ∅-axiom ✓ (`#print axioms`) |
| recurrence / rational-GF residue (Fibonacci) | `Lib/Math/Algebra/Mobius213/Px/FibonacciAtomicLock.lean:34` `fib` (`fib(n+2)=fib(n+1)+fib(n)`); `…/MobiusSelfForm.lean:119` `mobius_iteration_master` | `mobius_iteration_master` ∅-axiom ✓ (`#print axioms`) |
| recurrence residue tag `q=±1` | `Lib/Math/Algebra/CassiniUnimodular.lean:163` `cassini_law_one_at_two_multipliers`; `ContinuedFraction/ContinuedFractionFloor.lean:140` `cfQn_fib` | prior (`golden_ratio.md`) |
| analytic GF = truncated polynomial (the paradigm) | `Lib/Math/NumberSystems/Complex/PowerSeries.lean:6-18` (docstring), `:41` `polyId_at_zero`, `:52` `cExp_zero_eq_one` | concrete defs, ∅-axiom by `rfl` |

`mass_conv`, `momentNum_conv`, `profileMean_conv`, `mass_Phi_profile`, `momentNum_Phi_profile`,
`geom_sum`, `summatory_mul`, `mobius_iteration_master`, `conv_one_at_0`, `catalanGF_table`, `xVar_at_1`
were re-checked this session via `#print axioms` → all "does not depend on any axioms". The
`ConvolveProfile` module builds clean (`lake build` succeeds).

## The formal power-series semiring — NOW CLOSED (pointwise, funext-free, ∅-axiom)

- **The formal-power-series semiring + the weld is now BUILT** (`Combinatorics/PowerSeriesSemiring.lean`,
  33/0 PURE, `#print axioms` → no axioms). Two findings: (i) `Meta/Nat/Convolution213.lean` *already*
  carried the pointwise GF semiring on `Nat→Nat` (`conv_comm`/`conv_assoc`/distributivity/two-sided unit
  `delta`/Leibniz), so the real work was the **weld**, not re-proving a semiring; (ii) the weld pivot is
  that *both* Cauchy products are the **same partial sum**: `conv_eq_cauchy` / `convolution_eq_cauchy`
  (`= Σ_{i≤n} fᵢ·g_{n-i}`), giving `gfConv_eq_conv` (the `GeneratingFunction.convolution` = the
  `Convolution213.conv`) and the transported semiring laws `conv_comm'`/`conv_assoc'`/`conv_one_*`/
  `conv_add_distrib_*` + the bundle `power_series_semiring` (`xVar` = the degree-1 grading generator). The
  **character homomorphisms** are proved: `massN_addSeq`/`momentDeg_addSeq` (additive), and ★
  `massN_toCoeffSeq_conv` — the **multiplicative `×↦·` character on the welded product**, transported from
  `ConvolveProfile.mass_conv` with no re-derivation; the list→sequence weld is `toCoeffSeq_conv`
  (`toCoeffSeq (f⋆g) = conv (toCoeffSeq f) (toCoeffSeq g)`, unifying `List Nat` and `Nat→Nat`). So "GF
  multiplication = convolution, with `mass` the multiplicative and `momentDeg` the additive character" is
  now a closed ∅-axiom semiring fact. **Honest residual:** the semiring is *pointwise* (`∀n, (f⋆g) n =
  (g⋆f) n`), not extensional function equality — extensional ring equality on `Nat→Nat` needs `funext` =
  `Quot.sound` (forbidden), so pointwise is the honest ∅-axiom carrier (and all downstream coefficient
  computation uses exactly that). (The `Catalan C(x)=1+x·C²` relation is asserted only as a
  *table* `catalanGF_table`, not proven as a `convolution` identity — a concrete witness of the missing
  associativity/distributivity.)

- **The analytic GF as a function of numeric `x` (radius of convergence, closed-form value, the rational
  function `x/(1−x−x²)` as a real map)** — the `Real213`-cut residue, located by the transcendental rule,
  not built. Same boundary as `zeta_euler.md`/`exponential.md`: the formal/combinatorial GF is
  residue-free; the analytic GF-as-a-function lives in the residue. Not claimed.

- **EGF normalization `1/n!` as a built reading** — conceptual: the per-size `1/n!` weight (the
  exponential-vs-ordinary distinction) is described as an `exponential.md`/`weight` parameter but not
  instantiated as a Lean object (no `EGF` type, no `aₙ/n!` coefficient reading). The OGF (`weight=1`) is
  the one with Lean anchors.
