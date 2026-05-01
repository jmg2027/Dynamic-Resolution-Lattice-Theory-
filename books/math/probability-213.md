# Probability 213

*An exposition in 213-internal vocabulary.*

The 213-native realisation of probability theory.  Six independent
paths converge to the same conclusion: **probability in 213 needs
neither σ-algebra nor measure-theoretic Choice**.  The atomic
counting, dyadic refinement, and cohomological measure machinery
already in 213 directly realise the operational content of
probability.

Companion volume to `analysis213.md`, `number-theory-213.md`,
`cohomology-213.md`, `linalg-213.md`.  Vocabulary: Raw, Lens,
atomic count, dyadic depth, FluxCut, bisectN, riemannSampleSum.

All theorems referenced are 0-sorry, 0-Mathlib, 0-Classical,
≤ {propext, Quot.sound}, as verified in `lean/E213/Physics/Substrate/`,
`lean/E213/Research/Real213*Cut*.lean`, and related files.

**Status**: This volume is *partially realised*.  Foundation paths
are in place; the probability-marathon proper (parametric
distributions, Bayes via Lens composition, etc.) is pending future
work.  See `blueprints/math/01_probability_213.md` for the full
roadmap.

---

## Part I — Why probability without σ-algebra

### Chapter 1.  The σ-algebra obstruction

Kolmogorov probability rests on a triple (Ω, ℱ, P) with ℱ a
σ-algebra of "measurable" subsets and P a countably additive
measure.  This setup carries inherent baggage:

  - **Choice is required**: Vitali constructs non-measurable sets
    using AC; without AC, the σ-algebra structure collapses.
  - **Countable additivity is uncountable in disguise**: any
    enumeration uses ℕ, but the *closure* under countable unions
    is supposedly justified by AC.
  - **σ-algebras are external**: nothing in nature *gives* you a
    σ-algebra — it is imposed structure.

213 sidesteps this entirely.  Probability emerges as *counting on
a finite atomic structure*, with the dyadic refinement giving
arbitrarily fine resolution.

### Chapter 2.  Six paths to probability in 213

Six independent constructions yield the operational content of
probability without ZFC's σ-algebra:

  1. **Atomic counting** (Physics Phase 2 `Pairs.lean`):
     P(AA) = 3/10, P(BB) = 1/10, P(AB) = 6/10.  K_{3,2}^{(c=2)}
     edge counts give probabilities directly.
  2. **Dyadic uniform distribution** (`bisectN`,
     `riemannSampleSum`): each level-n bracket has measure 1/2^n.
  3. **Cohomological measure** (FluxCut): forward/backward flux
     give signed measure; ∂²=0 gives mass conservation.
  4. **Lens-output distribution**: Lens.view applied to Raw gives
     induced distribution on the codomain.
  5. **Trajectory frequency**: ArithFSM signature trajectory's
     visit-frequencies give distribution on Fin 5.
  6. **Cup product**: cohomology cup gives joint-distribution
     coupling (independence vs correlation reading).

Each is constructively realised in existing Lean files.  The book's
Parts II–V trace each path.

---

## Part II — Atomic counting

### Chapter 3.  K_{3,2}^{(c=2)} edge probabilities

The atomic edge inventory of K_{3,2}^{(c=2)} gives the simplest
probabilistic structure in 213.  Total edges:

  |E| = c · NS · NT = 2 · 3 · 2 = 12

Pair classes:

  - SS pairs: C(NS, 2) · 0 = 0  (no S-S edges in bipartite)
  - TT pairs: C(NT, 2) · 0 = 0  (no T-T edges either)
  - ST pairs: NS · NT · c = 12  (all edges are S-T)

In the *vertex-pair* counting (not edge-pair):

  - AA pairs (both S): C(3, 2) = 3  out of C(5, 2) = 10  → 3/10
  - BB pairs (both T): C(2, 2) = 1  out of 10            → 1/10
  - AB pairs (mixed): 3 · 2 = 6  out of 10               → 6/10

These are *not* defined probabilities — they are *counted* atomic
ratios.  See `Physics/Substrate/Pairs.lean`.

### Chapter 4.  Atomic distribution as Lens output

For any Lens α with view applied uniformly to Raw, the induced
distribution on α-image is *forced* by the structure of the Lens.
For α = Fin 5 with K_{3,2}^{(c=2)} signature lens:

  P(visit S₀, S₁, S₂) collectively = NS / d = 3/5
  P(visit T₀, T₁) collectively = NT / d = 2/5

Even atomic counting is therefore a Lens-output statement.  No
"random sampling" needed — the distribution is purely structural.

---

## Part III — Dyadic uniform distribution

### Chapter 5.  Bisection refinement

The dyadic refinement is implemented constructively.  Starting
from the unit bracket [0, 1] (in Real213 sense), `bisectN n`
produces 2^n equal sub-brackets, each of measure 1/2^n.

  bisectN : ℕ → List Bracket
  bisectN 0 = [unitBracket]
  bisectN (n + 1) = bisectN n |>.bind bisect

(`Research/Real213*.lean` family.)

This is the 213-native counterpart of "uniform distribution on
[0, 1]" in Lebesgue measure theory — but realised purely through
finite list operations, no σ-algebra.

### Chapter 6.  Riemann midpoint sampling

`riemannSampleSum f n` evaluates a function f at the 2^n midpoints
of the dyadic refinement and sums.  This is *constructive*
expectation — no measure axiom needed:

  E_n[f] := riemannSampleSum f n / 2^n

As n → ∞ in the Real213 sense, E_n[f] approaches the constructive
integral of f.  The whole expectation operator is a finite
arithmetic operation at any concrete depth.

### Chapter 7.  Probability = constant function expectation

For an event indicator I_E, the probability P(E) is just E[I_E]:

  P(E) = E[I_E] = (count of midpoints in E) / 2^n

This realises probability as *counting* in the limit.  No
measurability questions arise — every concrete depth gives a
well-defined integer count.

---

## Part IV — Cohomological measure (FluxCut)

### Chapter 8.  Flux as signed measure

The FluxCut framework (`Research/Real213FluxCut*.lean`) defines:

  fluxAlong : Function → Bracket → ℕ × ℕ   -- (forward, backward) pair
  fluxBalance : forward = backward + δ      -- ∂² = 0 form

The forward and backward flux give signed contributions; their
sum (in the Real213 sense) is the integral of the function over
the bracket.

Crucially: **mass conservation = ∂² = 0**.  The flux conservation
law of probability ("total mass = 1") is a cohomological identity,
not an axiom imposed externally.

### Chapter 9.  Probability measure normalisation

A probability measure P satisfies P(Ω) = 1.  In FluxCut form:

  total_flux := fluxAlong 1 unitBracket = 1

This is a 0-axiom theorem (constant function 1 over [0, 1] gives
total flux 1 by direct computation).  No σ-algebra closure axiom
needed.

The conditional probability P(A | B) = P(A ∩ B) / P(B) becomes
the *flux ratio* over sub-brackets — again a constructive ℕ × ℕ
arithmetic statement.

---

## Part V — Trajectory probability

### Chapter 10.  ArithFSM signature visit-frequency

For an ArithFSM-generated trajectory on K_{3,2}^{(c=2)} (signature
lens), the visit-frequency of each Fin 5 vertex over a finite
horizon gives a discrete distribution.

For Pell trajectories, the frequencies stabilise quickly due to
periodicity.  E.g., `pellFSMmod3` has TIGHT signature period 4;
the long-run visit-frequency on Fin 5 is uniform over the visited
subset.

The formal statement: signature-trajectory-frequency converges to
a Class C distribution determined by atomic counting (NS, NT, d).

### Chapter 11.  Bipartite alternation gives 50/50 S-T

The bipartite alternation invariant (`Math/Cohomology/Dyadic
SignatureBipartite.lean`):

  signature.bits even-step → S-side (NS = 3 choices)
  signature.bits odd-step  → T-side (NT = 2 choices)

Over long horizons, exactly half the steps are S, half T.  This
is the *deterministic* form of the "fair coin" abstraction —
realised by the structure of K_{3,2}^{(c=2)}, not by sampling.

---

## Part VI — Universal Lens applied to probability

### Chapter 12.  q213Lens-induced distribution

The universal lens `q213Lens : Lens (Q213 × Q213)` injects Raw
into rational pairs.  The induced distribution on Q213 × Q213
(when Raw is "sampled" via some Lens) is itself a Lens-output
distribution.

Universality means: the distribution on Q213 × Q213 carries the
*full* information of the original Raw distribution — no coarse-
graining loss.

This is the *probabilistic* form of the universality result: the
Lens framework preserves probability information faithfully.

### Chapter 13.  Cup product as joint distribution

The cohomology cup product ⌣ : Cⁿ × Cᵐ → Cⁿ⁺ᵐ has a
probabilistic reading: when α and β are *probability cochains*
(fluxes summing to 1 over their respective brackets), α ⌣ β is
the joint distribution.

  α ⌣ β = α(σ_front) · β(σ_back)

Independence corresponds to *cup-decomposability*; correlation
corresponds to non-trivial cup classes.  See `cohomology-213.md`
Part III for the cup machinery.

This realises probability *coupling* (in Wasserstein sense) as a
cohomological structure.

---

## Part VII — Open horizons

### Chapter 14.  Parametric distribution families

The natural next step: parametric distribution families
(Bernoulli, Binomial, Poisson, Normal) realised in 213.

The Bernoulli family is immediate — Bernoulli(p) for p ∈ Q213 is
the distribution on {0, 1} with P(1) = p.

Binomial(n, p) is `combine_n` over n independent Bernoulli(p)
samples.  Closed-form expectation E[X] = n · p in Q213
arithmetic.

Poisson and Normal are limits — they require Real213 closure
(Bishop-style) at the appropriate scale.  Open work.

### Chapter 15.  Bayes via Lens composition

Bayes' rule  P(A | B) = P(B | A) · P(A) / P(B)  becomes a
*Lens composition* statement.  Given:

  L_A : Lens α   (prior on hypothesis α)
  L_B : Lens β   (likelihood model)

The posterior Lens `L_{A | B}` is the composition under cup
product, normalised by the joint flux.

Conjectural framework: the entire Bayesian inference machinery
is `lens_composition_period`-style structural.

### Chapter 16.  Probabilistic falsifier track

The 213 probabilistic prediction track uses these foundations to
state *measurable* probabilistic claims.  Examples:

  - JUNO neutrino mass ordering: framework predicts specific
    P(NH) > 0.95.  Falsifier: experimental measurement.
  - θ_QCD ~ 10⁻¹¹: probabilistic upper bound; falsifier =
    nEDM measurement.

These remain open; their formalisation is part of the
`falsifier_213.md` track (physics side, not in this volume).

---

## Appendix A.  Lean theorem index

Foundation theorems (all ≤ {propext, Quot.sound}):

- `pair_count_AA_3_10`, `pair_count_BB_1_10`, `pair_count_AB_6_10`
  — atomic edge probabilities
- `bisectN_measure_uniform` — dyadic refinement
- `riemannSampleSum_correct` — constructive expectation
- `flux_balance` — ∂² = 0 mass conservation
- `q213Lens_is_universal` — Lens-output distribution faithfulness

Source files:
- `Physics/Substrate/Pairs.lean`
- `Research/Real213*.lean` (FluxCut, bisection, sampling)
- `Math/Cohomology/Dyadic*.lean` (signature trajectories)
- `Meta/UniversalLensQ213Inj.lean`

## Appendix B.  Verification standard

Every theorem closed in Lean 4 at:

  ≤ {propext, Quot.sound}    (Lean kernel floor), OR
  STRICT 0-AXIOM             (concrete enumerations, edge counts)

No `sorry`, no Mathlib, no Classical, no native_decide.

`cd lean && lake build` passes.

## Author

Mingu Jeong (Independent Researcher).

Acknowledgments: Claude (Anthropic) provided formalization
assistance under direct supervision.
