# Probability Brackets 213 — Blueprint

**Priority**: ★★★ (frontier F1 + F8 of
`research-notes/frontiers/research_program_year_horizon.md` — "the most
213-native of all the absences").  Implements topic **F1** (de Moivre–Laplace
bracket) with **F8** (finite information theory) folded in as Phase PD.

---

## 1. Why This Field

Classical probability:
- σ-algebra + countably-additive measure + Radon–Nikodym
- random variable = measurable function; distribution = pushforward
- limit theorems as *weak convergence* to continuum objects (the Gaussian)

None of that is the operand here.  213-native probability:
- **Probability = the ratio-Lens on counts**: favorable/total, a
  `ProbabilityCut` (`num`, `den`, `0 < den`, `num ≤ den`) — already the
  corpus's foundation (`Lib/Math/Probability/Foundation/Cut.lean`).  No
  σ-algebra ever appears; nothing is "measured", only counted and compared.
- **A limit theorem = a two-sided computable bracket with explicit modulus.**
  The residue-shape doctrine (`the_form_of_the_residue.md` "Infinity is the
  residue's shape"): the Gaussian limit is not a target the binomial
  approaches — it is the *shape of a narrowing rational bracket*, and
  **sharpening the bracket IS the math**.  Precedent, already ∅-axiom:
  `chebyshev_constant_interval` (`Lens/Number/Nat213/ChebyshevLower.lean`)
  traps `log₂ e` in the evaluable interval `[(m+1)/(2(m+2)), 6]` — the
  constant is a computed interval, not a deified point.
- **Independence = product structure of the count.**  `joint.num =
  a.num * b.num`, `joint.den = a.den * b.den`
  (`Foundation/Independence.lean`) — independence is not a condition *on* a
  measure, it is the statement that the total count factors, i.e. the
  incidence-Fubini double-count exchange
  (`Lib/Math/Combinatorics/IncidenceFubini.lean`, `genSwap`) applied to the
  outcome grid.  Fubini for the dyadic measure layer is frontier F2; this
  blueprint uses only the finite-grid form.

The decisive advantage: the corpus's Chebyshev prime-counting arc
(`theory/math/numbertheory/chebyshev_prime_counting.md`) already built the
exact machinery the flagship needs.  `central_binom_ge_two_pow`
(`2^n ≤ C(2n,n)`) and `four_pow_le_succ_mul_central_binom`
(`4^n ≤ (2n+1)·C(2n,n)`), both in `Lens/Number/Nat213/MultSystemValue.lean`
and both ∅-axiom, are **exactly the `k = 0` case of de Moivre–Laplace**:

```
4^n/(2n+1)  ≤  C(2n,n)  ≤  4^n        i.e.   1/(2n+1) ≤ C(2n,n)/4^n ≤ 1
```

The central term of the fair-coin walk is already bracketed.  Phase PB
extends the bracket from the peak to the whole profile `k ≠ 0`.

## 2. 213-native Emergence

### 2.1 Probability is a Lens reading, not an ontology

`ProbabilityCut` = a directed count-pair `(num, den)` read through the
ratio-Lens.  The tuple is the object (`slot_arithmetic.md` "Ontology");
`1/2` and `n/2n` are related by a relation, not collapsed by default.
"Event", "outcome", "sample space" are count-Lens vocabulary for finite
distinguishings — `List Bool` outcomes, `countTrue` counts
(`Foundation/SampleMean.lean`).

### 2.2 A limit theorem is a bracket, not a convergence

There is no continuum Gaussian to converge *to* (no exterior, §5.1).  The
theorem "binomial → Gaussian" is rebuilt as: two evaluable rational kernels
`lowKer n k ≤ C(2n,n+k)/4^n ≤ highKer n k` whose ratio `highKer/lowKer`
is itself bounded by an explicit function of `n` — **the bracket width is
the theorem**.  The modulus `N(ε)` (how far to compute for a given width)
is the computable operand; the "Gaussian" names the bracket's shape.

### 2.3 Independence = count factorization

A product experiment's total count is a grid count; the two marginal
readings are the two `genSwap` summation orders.  "Independent" is not a
property added to a distribution — it is the *definition* of running the
count on a product grid.  Correlation = failure of the grid to be a
product (a relation on the grid, counted).

### 2.4 Entropy = modulus degree

`MaxEntropy.lean` already defines `MaxEntropy s := ¬ FiniteHandle s`
(no polynomial-depth handle reaches the sequence) — entropy as *how hard a
pointing must work*, the modulus-degree reading
(`research-notes/frontiers/modulus_degree_crossdomain.md`: modulus degree =
certificate depth = receipt count of the pointing).  Shannon entropy of a
finite distribution is the finite shadow: the dyadic bisection depth needed
to name an outcome (`Information/Entropy.lean`,
`shannonEntropy_uniform_eq_depth`).  Phase PD turns this from uniform-only
`rfl` facts into counting theorems (Kraft, subadditivity).

## 3. Building Blocks

| Tool | Location | Use |
|---|---|---|
| `ProbabilityCut`, `complement`, `toFlux` | `Lib/Math/Probability/Foundation/Cut.lean` | count-ratio semantics |
| `joint` num/den product | `Foundation/Independence.lean` | independence = count factorization |
| `countTrue`, sample mean | `Foundation/SampleMean.lean`, `Limit/LLN.lean` | frequency counts |
| `central_binom_ge_two_pow`, `four_pow_le_succ_mul_central_binom` | `Lens/Number/Nat213/MultSystemValue.lean` | the `k = 0` de Moivre–Laplace bracket, proven |
| `vp_central_binom_le_floorLog`, `central_binom_le_pow_primePi` | `Lens/Number/Nat213/ChebyshevLower.lean` | central-binomial estimate patterns |
| `chebyshev_constant_interval` | `Lens/Number/Nat213/ChebyshevLower.lean` | the constant-as-interval precedent (`log₂ e`) |
| `genSwap` double-count exchange | `Lib/Math/Combinatorics/IncidenceFubini.lean` | product-grid marginals |
| `binom` symmetry/recursion | `Meta/Nat/BinomSymm.lean`, `Lib/Math/NumberTheory/BinomChooseBridge.lean` | ratio recursion for the profile |
| Markov/Chebyshev inequality skeletons | `Inequality/Markov.lean`, `Inequality/Chebyshev.lean` | tail-bound scaffolding |
| `shannonEntropyUniformBits`, `optimalCodeLength` | `Information/{Entropy,Coding}.lean` | entropy anchors |
| `MaxEntropy`, `maxEntropy_not_surjective` | `Probability/MaxEntropy.lean` | entropy = modulus degree |

## 4. Phase Plan

### Phase PA — Consolidation + honest audit (3-5 commits)

The `Lib/Math/Probability/` tree (5 sub-clusters + `Information/` +
`MaxEntropy.lean`) is real but its *limit* modules are placeholders.  Audit
findings to state cleanly and fix:

1. **LLN is currently witness-exact, not a law.**  `Limit/LLN.lean` proves
   exact count identities on *constructed* balanced sequences
   (`balancedHeadsTails`, `fair_LLN`); `Limit/LLNCauchy.lean`'s
   `fairLLN_cauchy` is a constant sequence with modulus `0`
   (`fairLLN_modulus_zero`) — the "law" holds because the sequence never
   deviates.  No statement quantifies over all outcomes with a deviation
   bound.  Record this as the gap Phase PE closes.
2. **`Distribution/Gaussian.lean` is degenerate**: `expSumAtZero_eq_one`
   evaluates the kernel only at 0; `CLT_fair_centered` is a marker.
   `Inequality/ChernoffGrade.lean` counts grade dimensions (`binom 5 g`),
   not tails.  Mark both as superseded targets of PB/PC.
3. State the **count-ratio semantics** in one place: a docstring-level
   contract on `ProbabilityCut` (tuple-is-the-object, relations not
   identities, complement/joint as count operations), and repair
   `Probability/INDEX.md`'s stale blueprint citation
   (`blueprints/math/01_probability_213.md` does not exist; this file is
   the successor).
4. Independence ↔ `IncidenceFubini`: one bridge theorem — the joint count
   of a product experiment equals both `genSwap` orders.

### Phase PB — Flagship: the de Moivre–Laplace bracket (8-12 commits)

Symmetric Bernoulli walk, `2n` steps.  Everything is a `Nat` inequality
(cross-multiplied; division-free like `chebyshev_constant_interval`).

1. **Ratio recursion (exact, W1)**:
   `C(2n, n+k+1) * (n+k+1) = C(2n, n+k) * (n-k)` — the walk profile as a
   telescoping product `C(2n,n+k) = C(2n,n) * ∏_{i<k} (n-i)/(n+i+1)`,
   kept as cross-multiplied `Nat` identities.
2. **Two-sided profile kernel**: define the rational kernels and prove
   `lowKer(n,k) * C(2n,n) ≤ C(2n,n+k) * D_low` and symmetrically above —
   candidate kernels: upper `∏_{i<k} n/(n+i+1)`, lower
   `∏_{i<k} (n-k)/(n+i+1)`; the Gaussian *shape* is the theorem that both
   kernels obey quadratic-exponent brackets (`(n²-k²)^k ≤ n^{2k}` -style),
   the discrete `e^{-k²/n}` silhouette with no `exp` anywhere.
3. **Compose with the proven peak bracket**: `k = 0` is
   `central_binom_ge_two_pow` + `four_pow_le_succ_mul_central_binom`
   verbatim.  Target flagship statement:

   ```
   deMoivreLaplace_bracket (n k) (h : k ≤ n) :
     lowNum n k * 4^n ≤ upDen n k * C(2n, n+k) * (2n+1)  ∧
     C(2n, n+k) * lowDen n k ≤ hiNum n k * 4^n
   ```

   with `lowNum/lowDen/hiNum/upDen` explicit polynomial/product values.
4. **The bracket width as a theorem**: `hi/low ≤ (2n+1) * (explicit poly)`,
   evaluable at every `(n,k)` — plus `#eval`-style instance rows for small
   `n` in the docstring (the interval computed, not asserted).

### Phase PC — Tail counts: Chernoff as counting (4-6 commits)

1. From PB's ratio recursion: for `j ≥ n+a` the term ratio is
   `≤ (n-a)/(n+a+1) < 1`, so the tail is majorized by a geometric series —
   `∑_{j≥n+a} C(2n,j) ≤ C(2n,n+a) * (n+a+1)/(2a+1)`, a pure `Nat`
   inequality (finite sum vs geometric majorant; no `exp`, no `log`).
2. Package: `tailCount`, `chernoff_tail_bracket` (two-sided where cheap:
   the largest term is also a lower bound).
3. Retire/absorb `ChernoffGrade.lean`'s placeholder framing; upgrade
   `Inequality/Markov.lean`/`Chebyshev.lean` from witness specializations
   to all-outcome count statements using `tailCount`.

### Phase PD — Entropy as counting (F8) (5-8 commits)

1. **Kraft inequality**: a prefix-free code = a family of disjoint dyadic
   subtrees; `∑ᵢ 2^(L-ℓᵢ) ≤ 2^L` is literally a leaf count — pure `Nat`,
   sits on `Information/Coding.lean`'s `optimalCodeLength`.
2. **Source-coding bound** as a count comparison: fewer than `2^k`
   codewords cannot separate `2^n` outcomes for `k < n` (pigeonhole,
   `Lib/Math/Combinatorics/Pigeonhole.lean`).
3. **Subadditivity** `H(X,Y) ≤ H(X) + H(Y)`: for dyadic distributions this
   is a counting statement via the log-sum inequality's *discrete bracket*
   (cross-multiplied; the only "log" is the bit-depth count, per
   `shannonEntropy_uniform_eq_depth`).  General rational case: bracket the
   entropy itself as an interval (the `chebyshev_constant_interval`
   pattern) and prove subadditivity of the bracket endpoints.
4. **Wire `MaxEntropy.lean` in**: a theorem linking finite entropy brackets
   to modulus degree — high entropy = high pointing cost
   (`modulus_degree_crossdomain.md` Bridge 1: modulus degree IS certificate
   depth).  Minimum: the uniform distribution maximizes the dyadic entropy
   count (finite MaxEntropy shadow).

### Phase PE — Payoff: the weak law with explicit modulus (3-5 commits)

1. From PC's tail bracket: `P(|countTrue/n - 1/2| ≥ ε) ≤ δ(n, ε)` with
   `δ` explicit rational and an **explicit `N(ε)`** — the modulus is the
   deliverable, not the limit (`fairLLN_modulus_zero`'s degenerate `0`
   replaced by a real computable modulus).  This is the genuine LLN the PA
   audit found missing.
2. Bridge to the physics branch: DRLT statistical readings (ensemble
   ratios, `K_{NS,NT}` observable averages) consume `ProbabilityCut`
   brackets; record the interface in one bridge file, no physics claims.

## 5. Honest Walls (state them; do not fudge)

- **No continuum Gaussian.**  `e^{-x²/2}/√(2π)` is never an operand.  The
  discrete kernel comparison IS the theorem; `√(πn)` appears only as a
  two-sided `Nat` bracket on `C(2n,n)·√n`-type products if ever needed.
- **No CLT-as-weak-convergence.**  No topology on distributions, no
  characteristic functions.  What is delivered: evaluable brackets with
  width theorems.  Anything phrased "converges in distribution" is W2 here.
- **`log`/`exp` only as bracket objects.**  The corpus's rule: `log₂ e`
  exists as the computed interval `chebyshev_constant_interval`; any
  entropy constant enters the same way (an interval, narrowing, evaluable)
  — never as an imported analytic function (External-ruler smuggling row).
- **Independence beyond product grids** (Markov chains, martingales) is out
  of scope; frontier F2 (dyadic Fubini) is the prerequisite for the
  measure-layer version.

## 6. Connections to Other Tracks

- **Chebyshev arc** (`chebyshev_prime_counting.md`): shared
  central-binomial engine; PB is its probabilistic re-reading.
- **IncidenceFubini / CountDuality**: independence = double-count exchange.
- **Modulus-degree ladder** (`modulus_degree_crossdomain.md`,
  `modulus_degree_ladder.md`): entropy = modulus degree (PD.4).
- **F7 games**: Bernoulli walk = the simplest game tree; shared `List Bool`
  substrate.
- **Physics branch**: statistical readings of DRLT observables (PE.2).

## 7. Success Criteria

1. `deMoivreLaplace_bracket` proven, ∅-axiom
   (`#print axioms` empty), with the width theorem and evaluable instances.
2. `chernoff_tail_bracket` proven as a pure counting inequality.
3. Kraft + source-coding bound + entropy subadditivity proven; `MaxEntropy`
   cited by ≥1 theorem, not only prose.
4. A weak law with explicit rational `N(ε)`, superseding the degenerate
   `fairLLN_modulus_zero`.
5. `Probability/INDEX.md` updated (stale blueprint reference repaired,
   Limit-cluster placeholders retired or absorbed).
6. Zero `sorry`, zero Mathlib, zero `Classical.*`; every flagship statement
   division-free or cross-multiplied.

## 8. Key Insights (★)

★ **The `k = 0` case is already in the repo** — de Moivre–Laplace's peak is
`central_binom_ge_two_pow` + `four_pow_le_succ_mul_central_binom`, proven
∅-axiom for the prime-counting arc.  The flagship is an *extension of an
existing bracket*, not a new theory.

★ **The bracket width is the theorem** — the Gaussian is the residue's
shape read off a narrowing rational interval, exactly as `log₂ e` is the
shape of `chebyshev_constant_interval`.

★ **Independence was never a measure condition** — it is the count
factoring, i.e. Fubini on a finite grid, and the corpus's `joint` already
says so.

## 9. First Marathon Command

```
"Start Phase PA.  Audit Lib/Math/Probability/ (LLN modulus, Gaussian/Chernoff
placeholders), state the count-ratio contract on ProbabilityCut, and prove the
joint ↔ IncidenceFubini bridge."
```
