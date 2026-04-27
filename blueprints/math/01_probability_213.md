# Probability 213 — Blueprint

**Priority**: ★★★ Top priority (atomic counting + dyadic + cohomology
— all three tracks already laid, lowest entry barrier)

---

## 1. Why This Field

ZFC probability theory (Kolmogorov axioms):
- Sample space Ω + σ-algebra + measure P
- Depends on Choice (Vitali non-measurable sets → trouble)
- σ-algebra enforces closure conditions (countable additivity)

Natural emergence in 213:
- **Cohomological measure framework already in place** (FluxCut)
- **Dyadic uniform distribution already in place** (bisectN, riemannSampleSum)
- **Atomic counting already in place** (d=5, 10 pairs, etc. — physics track)
- *σ-algebra unnecessary* — dyadic structure itself is a measurable space

## 2. 213-native Emergence — 6 Paths

### 2.1 Atomic counting (most direct)

Physics track Phase 2 `Pairs.lean` already in hand:
- P(AA pair) = 3/10
- P(BB pair) = 1/10
- P(AB pair) = 6/10 ← K_{3,2} bipartite

**Counting is probability**.  DRLT's "Algebraic Priority" principle.

### 2.2 Dyadic uniform distribution

`unitBracket` + `bisectN`:
- P(leftHalf) = 1/2
- P(depth-n bracket) = 1/2^n

`riemannSampleSum` is *midpoint sampling* — constructive form of
Cantor-style uniform distribution.  Already has propEq closed form.

### 2.3 Cohomological measure (FluxCut → measure)

This marathon's `FluxCut`:
- forward / backward = positive / negative measure component
- `fluxBalance` = mass conservation (∂² = 0)
- `fluxAlong f db` = flux of f over db (= integral measure)
- normalization: total flux = 1 → probability measure

**Measure = 1-cochain**.  Operates without σ-algebra.

### 2.4 Cauchy convergence → Law of Large Numbers

`CauchyCutSeq` + `partialSum`:
- mean = `partialSum / n`
- convergence = Cauchy
- LLN directly expressible

### 2.5 Bayesian update (cut-query)

Each query (m, k) on cut → Bool.  Without knowing the underlying
value, accumulate query results → update posterior.  Bayesian
without σ-algebra.

### 2.6 Gaussian / CLT

Gaussian = transcendental.  exp(-x²/2) at peak: propEq possible
via the exp(0) = 1 pattern from this marathon.  CLT = partial sum
convergence (infrastructure already in place).

## 3. Already-Laid Building Blocks

| Tool | Module | Purpose |
|---|---|---|
| `cutSum`, `cutMul`, `cutDiv` | `Real213CutSum/Mul/Inv` | measure arithmetic |
| `partialSum` | `Real213CutSeries` | E[X], summation |
| `riemannSampleSum` | `Real213DyadicRiemann` | integration (uniform distribution) |
| `FluxCut` + `cohomEquiv` | `Real213FluxCut/Equiv` | measure = 1-cochain |
| `IsAntiderivative` | `Real213Antiderivative` | CDF (cumulative distribution) |
| `dyadicIntervalAB` | `Real213IntegralDyadic` | arbitrary dyadic interval |
| `expTermsAtZero` | `Real213ExpAtZero` | Gaussian peak |

## 4. Phase Plan (Concrete)

### Phase EA — Foundational structure (4-6 commits)

1. **`IsProbabilityCut`** — normalized FluxCut: `∫ = 1`
2. **`UniformOnUnit`** — `P([a/2^E, b/2^E]) = (b-a)/2^E` propEq
3. **`Bernoulli`** — `P(X = 1) = p`, using atomic 2-block
4. **`Binomial`** — n Bernoulli trials, atomic counting

### Phase EB — Expectation + Variance

1. **`Expectation`** = reinterpretation of `IsAntiderivative.integral`
2. **`Variance`** = `∫ (X - E[X])^2 dx` (square via cutMul x x)
3. Uniform [0,1]: E[X] = 1/2, Var[X] = 1/12 (cohomEquiv)

### Phase EC — Law of Large Numbers

1. **`SampleMean n samples`** = `partialSum / n`
2. **`LLN_unit`** — sample mean of uniform → 1/2 (Cauchy form)

### Phase ED — Bayesian framework

1. **`PosteriorUpdate`** — belief distribution update after cut-query
2. Beta distribution generalization (using atomic counting)

### Phase EE — CLT + Gaussian

1. **`gaussianTermsAtZero`** — exp(-x²/2) at x=0 = 1 (peak)
2. **`CLT_skeleton`** — normalized partial sum → Gaussian form

### Phase EF — Capstone

`phaseEX_probability_capstone` — 18+ fact bundle.

## 5. Connections to Other Tracks

- **Physics track Phase 2** (`Pairs.lean`): direct use of K_{3,2} distribution
- **CKM/PMNS** (standard-model/): unitary mixing → transition probabilities
- **η_B** (cosmology/): 6×10⁻¹⁰ baryogenesis = very small probability
- **Critical line / RH**: GUE/GOE statistical distributions
- **Yang-Mills**: spectral measure = measure = FluxCut
- **DHA** (discrete-harmonic): discrete measure theory

## 6. Open Problems

- **Measurable function without σ-algebra** — is dyadic alone sufficient?
- **Cauchy form for continuous distributions** — generalized Gaussian, exp, etc.
- **Independence** definition: via tree branching?
- **Conditional expectation** = sub-flux

## 7. Key Insights (★)

★ **Probability = atomic counting + cohomological flux + dyadic
trajectory**.  ZFC's Ω, σ-algebra, Choice are all *unnecessary* —
naturally derived from structures 213 already possesses.

★ **Vitali paradox disappears = feature**.  Without Choice, non-measurable
sets cannot exist at all.

★ **Resembles Bishop constructive probability but goes deeper** — built
on dyadic axioms, not on ZFC.

## 8. First Marathon Command

```
"Start Phase EA.  Define IsProbabilityCut + UniformOnUnit propEq + Bernoulli atomic"
```

Entry analogous to Phase J of Analysis 213.  Phase EA completes in 4-6 commits.

