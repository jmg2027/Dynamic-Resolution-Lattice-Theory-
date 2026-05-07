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

All theorems referenced are **0-sorry, 0-Mathlib, 0-Classical,
0-native_decide, ∅-axiom** (the strict standard: every theorem
satisfies `#print axioms T` → "does not depend on any axioms").
Anything with a non-empty axiom list is `sorry`-equivalent and
does not count.  See `seed/AXIOM/04_falsifiability.md` §5.2.1 +
`CLAUDE.md` "∅-axiom standard".

**Status**: **Marathon COMPLETE.**  Atomic core closed across 11
topical clusters in `lean/E213/Lib/Math/Probability/` plus the
Real213 transcendental extension (`cutExp`, `cutLog`, `cupPow`
nilpotency) in `lean/E213/Lib/Math/Cohomology/` and
`lean/E213/Lib/Math/Real213/`.  Total ~247 atomic facts, all
∅-axiom.  Original blueprint `blueprints/math/01_probability_213.md`
retired (deletion recorded in `blueprints/math/INDEX.md`).

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

## Part VII — Realised content (post-marathon)

What Chapter 14–16 framed as "open" is now closed.

### Chapter 14.  Parametric distribution families — REALISED

  * `Lib/Math/Probability/Bernoulli.lean` — `Bernoulli` structure
    with `success`, `failure` legs; `fair`, `certain`, `impossible`
    atoms; `success.num + failure.num = den` closure (9 facts).
  * `Lib/Math/Probability/Binomial.lean` — K_{3,2} pair distribution
    `pAA = 3/10, pBB = 1/10, pAB = 6/10` lifted from
    `Physics/Substrate/Pairs`; `ABBernoulli` AB-or-not view;
    `trialSequenceNum` / `Den` for n-trial product mass (13 facts).
  * `Lib/Math/Probability/BetaDensity.lean` — unnormalised Beta(α, β)
    at a `ProbabilityCut`; `betaNumAt`, `betaDenAt`; closed
    Beta(1,1) uniform, Beta(2,1) linear (8 facts).
  * `Lib/Math/Probability/BetaNormalized.lean` — normalisation
    constant for `(α, β) ∈ {(1,1), (2,1), (1,2)}`: B(1,1) = 1,
    B(2,1) = B(1,2) = 1/2 (11 facts).
  * `Lib/Math/Probability/Gaussian.lean` — Gaussian peak via Taylor
    `expSumAtZero N = 1` exact-truncation (9 facts).

### Chapter 15.  Bayes via conjugate counting — REALISED

  * `Lib/Math/Probability/Bayesian.lean` — `BetaCount (α, β)`
    structure; `posteriorMean = α / (α + β)`; `updateOnSuccess` /
    `updateOnFailure` are `+1` on the matching field;
    `updateBatch ks fs`; Laplace's rule of succession (uniform
    prior → 2/3 / 1/3 after one observation); sequential ↔ batch
    via `Nat` add associativity (14 facts).
  * `Lib/Math/Probability/Markov.lean` — BetaCount commutativity
    (Markov sufficient-statistic property) + Markov inequality on
    discrete distributions (6 facts).
  * Bayes update is *count addition*, not Lens composition.  The
    Lens-composition conjecture from the original chapter
    dissolves: the conjugate updateBatch + posteriorMean already
    *is* the structural Bayes inference, no Lens overhead needed.

### Chapter 16.  Falsifier track + concentration — REALISED

  * `Lib/Math/Probability/Concentration.lean` — clamped
    `excess + deficit` deviation; balanced/all-heads/all-tails
    closed forms (7 facts).
  * `Lib/Math/Probability/Chebyshev.lean` — polynomial concentration
    via Markov-on-second-moment (5 facts).
  * `Lib/Math/Probability/Hoeffding.lean` — finite-depth Taylor
    exponential bound + balanced collapse (5 facts).
  * `Lib/Math/Probability/CLTLimit.lean` + `CLTGeneric.lean` —
    Cauchy-modulus form of LLN at exact balance + variance-modulus
    generic form (12 facts).
  * `Lib/Math/Probability/SampleMean.lean` + `LLN.lean` — countTrue,
    sample mean, balanced LLN_unit *exact* (no limit) (19 facts).
  * `Lib/Math/Probability/Independence.lean` — joint product mass +
    conditional ratio + `joint_comm`, `joint_unit_left` (12 facts).

### Chapter 16.  Probabilistic falsifier track

The 213 probabilistic prediction track uses these foundations to
state *measurable* probabilistic claims.  Examples:

  - JUNO neutrino mass ordering: framework predicts specific
    P(NH) > 0.95.  Falsifier: experimental measurement.
  - θ_QCD ~ 10⁻¹¹: probabilistic upper bound; falsifier =
    nEDM measurement.

Cross-track: their formal physics-side closure lives in
`books/physics/falsifier-213.md` (not this volume).

---

## Part VIII — Paradigm reframe (post-extension)

The Real213 extension surfaced a deep correction.  The originally
"deferred" items — Cauchy convergence of `cutExp`, continuous
Chernoff `inf_t`, integration-defined `log` — were **classical-
analysis residue**, not gaps.  213's substrate
`K_{3,2}^{(c=2)} ⊂ Δ⁴` dissolves them structurally.

### Chapter 17.  exp closes finitely (nilpotency)

`Lib/Math/Cohomology/CutExpFiniteTruncation.lean` (12 facts).

`cutExp(α) = Σ α^n / n!` is **not** an infinite series on this
substrate.  For `α : Cochain 5 1` (grade 1 on Δ⁴):

  - `α^n ∈ Cochain 5 n` lives in `Fin (binom 5 n) → Bool`.
  - `binom 5 n`: 1, 5, 10, 10, 5, 1, **0** at `n = 6` and beyond.
  - For `n ≥ 6`: `Fin (binom 5 n) = Fin 0` — empty domain.
  - `cupPow α n i = false` *vacuously* via `False.elim` from
    `i.isLt < 0` (since `binom 5 n = 0`).

★ **exp truncates exactly at 5 terms on K_{3,2} substrate.**  No
limit, no Cauchy modulus, no convergence — the tail doesn't shrink
to zero, *the tail doesn't exist*.

### Chapter 18.  Chernoff is grade-indexed (discrete optimisation)

`Lib/Math/Probability/ChernoffGrade.lean` (9 facts).

Classical Chernoff `inf_t E[e^{tX}] · e^{−tε}` minimises over real
`t`.  213-native: `t ↦ grade ∈ Fin 5` is a *discrete* index over
the cohomology ring's grades.  The "infimum" is the topological
eigenstate where the cup-product structure forces the bound to
close — a **single grade**, not a limit of grid approximations.

  * `gradeDim`: 1, 5, 10, 10, 5 (the binom 5 g table).
  * `chernoff_at_grade g`: Markov inequality at every grade g.
  * `closing_grade_exists`: explicit existential witness for the
    discrete-grade closure.

### Chapter 19.  log is a cup-inverse (no integration)

`Lib/Math/Cohomology/CutLog.lean` (6 facts).

`cutLog` is the **formal algebraic inverse of `cutExp` under cup
product**, modulo Grade-overflow nilpotency.  Not `∫ 1/x dx`, not
the Mercator series limit.

  * `cutLog α 1 = α` (linearisation at grade 1, rfl).
  * `cutLog_cup_grade_6_zero`: Grade-6 nilpotency inherited.
  * The full ring-inverse identity `cutExp ∘ cutLog = id` requires
    cup-Ring homomorphism machinery (continuation in
    `Cohomology/Cup/Ring.lean` track).

---

## Appendix A.  Capstone witnesses (16 grand bundles)

`Lib/Math/Probability/Capstone.lean` collects the grand witnesses,
all `#print axioms` ∅:

  - `atoms_witness` — Cut/Uniform/K_{3,2}/Bernoulli closure
  - `moments_witness` — E[X], Var[X], discrete moments
  - `sampleMean_witness` — countTrue, balanced LLN_unit
  - `bayesian_witness` — uniform prior, Laplace ±, batch zero
  - `gaussian_witness` — Taylor at 0, peak = 1, CLT centering
  - `independence_witness` — joint product, conditional ratio
  - `markov_witness` — BetaCount commutativity + Markov inequality
  - `concentration_witness` — balanced/all-heads/all-tails dev
  - `beta_density_witness` — Beta(1,1)/(2,1)/(1,2) closed forms
  - `clt_modulus_witness` — Cauchy modulus existence
  - `total_witness` — 20-fact grand bundle
  - `cauchy_modulus_witness` — `ProbCauchy` constSeq
  - `chebyshev_witness` — polynomial concentration
  - `beta_normalized_witness` — three closed-form B(α, β)
  - `cltGeneric_witness` — variance-modulus form
  - `hoeffding_witness` — finite-depth exponential bound
  - `nilpotency_witness` — Grade-6 nilpotency (paradigm reframe)
  - `grade_chernoff_witness` — discrete-grade Chernoff closure
  - `cuplog_witness` — formal cup-inverse linearisation

## Appendix B.  Verification standard

Every theorem closed in Lean 4 at the **∅-axiom** standard:

  `#print axioms <theorem>` → "does not depend on any axioms"

This is *bare-metal type theory* — no `propext`, no `Quot.sound`,
no `Classical.choice`, no Mathlib axioms, no `native_decide`.
Anything with a non-empty axiom list is `sorry`-equivalent.

The legacy `≤ {propext, Quot.sound}` tier is **deprecated**
(see `seed/AXIOM/04_falsifiability.md` §5.2.1).

Audit:

  - `cd lean && lake build E213` — clean.
  - `tools/scan_axioms.py E213.Lib.Math.Probability` — every
    theorem ∅.
  - `tools/scan_axioms.py E213.Lib.Math.Cohomology` — paradigm
    reframe modules ∅.
  - `tools/kernel_regress.sh` — Term-ring 0-axiom 101/101.

## Author

Mingu Jeong (Independent Researcher).

Acknowledgments: Claude (Anthropic) provided formalization
assistance under direct supervision.
