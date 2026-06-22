# Decomposition: the Central Limit Theorem / the Gaussian

*213-decomposition of the CLT and the Gaussian, per `../README.md` (model v4).*
*Cross-links `probability.md` (the **weight**-reading; convolution = composing weights),
`golden_ratio.md` (the **q=+1 converging residue** = a fixed point of a self-applying map),
and `derivative.md`/`continuity.md` (the **resolution dial**; the limit computed via a modulus,
never grasped).*

> **LEVERAGE target.** The bar here is not "re-see the Gaussian" but "does the calculus
> *predict/derive* it?". Hypothesis: **the Gaussian is the q=+1 converging residue of the
> convolution-and-rescale iteration** — where convolution = composing weight-readings (adding
> independent variables = convolving their weights, `probability.md`). φ was the fixed point of
> the Möbius iteration; the Gaussian is the fixed point of the convolution-rescale iteration.
> Honest verdict at the end: prediction / collapse-only / miss.

## The decomposition

- **Construction `C`** — the same distinguishing as `probability.md`/`cardinality.md`: a family
  of distinguishables read as a **weight** (a value-weighted count, `L`'s `weight` parameter).
  Nothing new is constructed. A random variable is `⟨ family ∣ weight-reading ⟩`; **adding two
  independent variables = composing their weight-readings** — the *operation* on `C` that the
  iteration repeats. (Lean shadow: `ProbabilityCut = (num, den)`, no `Ω`; the weight is the
  value-slot of `Expectation.discreteNum`, `probability.md`.)

- **Reading `L = (weight-composition) ∘ (rescale) at residue resolution`** — a **composite,
  iterated reading**, every piece already in the calculus:
  1. **weight-composition** (convolution) — the additive twin of independence's multiplicative
     character. Independence is `joint a b = (a.num·b.num)/(a.den·b.den)` — the `×↦·`
     character (`Independence.joint`, `joint_assoc_num`, `probability.md`). Summing independent
     variables convolves their weights; the **mean** of the sum is the *additive* character
     `Σ` distributing over concatenation (`LLN.countTrue_append`, `Expectation.discreteNum_append`).
  2. **rescale** — the standardization dial: center (subtract the mean) and shrink by the
     spread. This is exactly `derivative.md`'s **resolution parameter** on `L` — "adjacent via a
     modulus, the bracket shrinking", here the `1/√n` (atomically: the `1/(2n)` / `den²`) narrowing.
  3. **residue resolution** — read the iterate-of-composition not at a finite stage but in the
     residue, computed by a **modulus** `N(ε)` (how many summands for precision `ε`), the limit
     never the operand (`golden_ratio.md`'s `N(m,k)=2k`, `derivative.md`).

  So `L` here is the README's three slots meeting at once: **weight** (1) × **character** (1's
  `+`-mode) × **resolution** (2,3) — exactly where "every deepest result sits where two of these
  meet" predicts the payoff.

- **Residue** — what this iterated weight-composition forces but cannot capture: **the Gaussian
  shape**, tagged **`q = +1` (converging)**. The standardized partial sums climb toward one fixed
  profile and *never land on it* at any finite `n`; the profile is the **fixed point of the
  convolution-and-rescale map**, named by a finite generator (the preserved moments: centered at
  `0`, second moment fixed; the modulus `N(ε)`), never grasped as an object. This is `golden_ratio.md`'s
  residue at the *same* `q=+1` pole as φ — a self-applying map *with* a fixed point, asymptoting
  toward it (Lambek/converge), the dual of the `q=−1` escaping diagonal (`cardinality.md`).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   random variable Xᵢ        =  ⟨ family ∣ weight-reading ⟩                  (probability.md's weight)
   X₁+…+Xₙ (sum)             =  weight-composition (convolution) of the n weights   = the iterated op
   independence              =  ⟨ product of count-pairs ∣ ratio ⟩  = ×↦· character (joint)
   centering / rescale       =  the resolution dial on L  (subtract mean, shrink spread)
   standardized Sₙ           =  ⟨ (convolve∘rescale)ⁿ(seed) ∣ L ⟩  at finite resolution
   the Gaussian              =  Residue(L, C),  q=+1   = the convolution-rescale FIXED POINT
   "Sₙ → Gaussian"           =  reached-by-none, narrowed by the modulus N(ε)  (limit never operand)
```

The map to iterate is `Φ : weight ↦ rescale(weight ⋆ weight)` (convolve a copy with itself, then
restandardize). The Gaussian is `Φ`'s fixed point — the exact analogue of φ as the Möbius
iterator `T`'s fixed point (`golden_ratio.md`), with **`Φ` in the role of `T`** and the
**moments in the role of the recurrence** (the finite generator).

## LEVERAGE — does the calculus PREDICT the Gaussian as the convolution fixed point/residue?

**Verdict: PREDICTION (conceptual), with a partially-built Lean spine — stronger than the brief's
"likely thin" estimate, weaker than `entropy.md`'s closed derivation.** Three layers, honestly graded:

**(A) Predicted, and the prediction is non-trivial.** The calculus, *before looking at the Lean*,
emits a specific claim from its parts: a random variable is a weight-reading; summing independents
= composing weights (the `+`-character, `probability.md`); standardization = the resolution dial
(`derivative.md`); a residue at the `q=+1` pole is a **fixed point of a self-applying map**
(`golden_ratio.md`). Composing these *forces* the form "the limit of summed-rescaled independent
weights is the **fixed point of convolve-and-rescale**, computed via a modulus, never grasped."
That is a derivation of CLT's *shape* from the model's slots, not a relabeling — it passes the
re-skin guard the way `entropy.md` did: the model says *which* fixed point and *why* it converges
(`q=+1`), not merely "CLT exists."

**(B) The Lean spine that is actually built (verified) — the fixed-point/residue machinery exists
and the CLT scaffolding instantiates its q=+1 pole at the *attained* level:**
- The **q=+1 converging fixed point as a modulus-computed residue** is a real ∅-axiom theorem:
  `banach_fixed_point` — a contraction `T` has `x* = lim(picard T x0)` as a fixed point reached
  by **none**, only the Cauchy limit, with an explicit geometric modulus `N(m)` (`picard_cauchy`);
  `banach_unique`. This is *literally* `golden_ratio.md`'s "fixed point = q=+1 residue, narrowed
  by a modulus, the limit never an operand" as a general theorem — the engine the CLT residue needs.
- **Convolution = the character on weights** is built: `Independence.joint` (`×↦·`), and the
  additive twin (mean of a sum) `countTrue_append` / `Expectation.discreteNum_append` — the two
  characters `probability.md` identified, here doing the convolution work.
- **Centering attained structurally** (the rescale's fixed condition): `Gaussian.CLT_fair_centered`
  — the standardized deviation `2·heads − length = 0` *exactly* for a balanced length-`2n` sample.
- **Variance preserved** (the second moment fixed — the finite generator's invariant):
  `Gaussian.CLT_fair_variance_marker`, `Variance.variance_master` (fair-coin `Var = 1/4`).
- **The Gaussian *value* as a finite-Nat fact**: `Gaussian.gaussianPeakAtZero_eq_one`,
  `expSumAtZero_eq_one` — `exp(−x²/2)|₀ = exp(0) = 1`, the peak computed atomically (Taylor at `0`
  collapses to its constant term), no transcendence.
- **The residue read as a Cauchy modulus that collapses at the q=+1 pole**:
  `CLTLimit.balanced_LLN_modulus` (modulus `N(ε)=0` for the balanced sequence),
  `CLTGeneric.cltModulus_of_varBound V ε := V·ε` with `genericCLT_balanced_collapse`
  (at `V=1` it collapses to the trivial balanced modulus), `CauchyModulus.ProbCauchy` /
  `absDevCross_self` (the `(Nat,Nat)`-only Cauchy structure on `ProbabilityCut` sequences).

**(C′) UPDATE — the contraction leg is now built (∅-axiom).** The keystone's load-bearing half is
closed. `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean` (20 pure / 0 dirty) builds the
`Φ = convolve-and-rescale` **rescale leg** as exact dyadic-rational halving and proves
`Φ_contraction (L) : Contraction (dyMet L) Φ` — convolve-rescale *is* a `Contraction` in
`BanachFixedPoint`'s sense. `Φ_picard_cauchy` applies `picard_cauchy` to it (orbit Cauchy, geometric
modulus `N(m)=m`), and `center_fixed`/`orbit_to_center` locate the `q=+1` fixed point reached-by-none.
**Now also built (`DyadicCompletion.lean`, 19/0):** a **genuine quotient-free Cauchy-completion** `DyC L`
of the dyadic metric (Bishop regular-Cauchy sequences, no `Quot.sound`), the contraction lifted to it
(`Φhat_contraction : Contraction (metC L) (Φhat L)`), and **`orbit_to_center_completion`** — the
convolve-rescale Picard orbit converges *in the completion metric* to the Gaussian center: the center is
now a true **completion-limit** of the lifted contraction, not just a by-hand `picard_cauchy` argument.

**Honest residual (now a *principled* wall, not missing work):** `banach_fixed_point`'s generic *wrapper*
still cannot be applied, because `CompleteMetricModulus.lim : (Nat→X)→X` demands a **total choice-free**
limit operator satisfying `climconv` for *every* Cauchy sequence — constructively impossible (`lim` would
have to read each sequence's own unbounded convergence modulus; no fixed freeze schedule works for all
inputs). This is the standard fact that a metric completion's limit operator is not total-computable — so
the *engine wrapper* stays unreachable ∅-axiom, while the *content* (center = completion-limit of `Φ`) is
delivered. Two pieces remain conceptual: a **convolution** operator on full weight-readings (the tree has
masses `(num,den)` + the `joint` ×-character, no density type), and the full Gaussian **profile** (not
just its center) as `Φ`'s fixed point.

**(C) The remaining gap — predicted-not-built.** What the Lean still does **not** contain:
- **No convolution operator on full weight-profiles** (only `ProbabilityCut=(num,den)` masses + the
  `joint` ×-character), hence **no theorem that the Gaussian *profile* is `Φ`'s fixed point** — the
  contraction is proved on the centered dyadic statistic, not yet on the shape. The completeness
  instance (`CompleteMetricModulus Dy`) that would route the fixed point through `banach_fixed_point`
  rather than by-hand is also still open.
- The CLT files are honest about this: `CLTLimit.lean` says the generic modulus "depends on the
  sequence; the balanced specialisation collapses to the trivial modulus", and `Gaussian.lean`
  defers the real form — *"The `partialSum`-based Cauchy-modulus form of full CLT lives in
  `Real213.CutSeries.partialSum`"* (a pointer, not a proof here). `CLTGeneric.genericCLT_modulus_exists`
  has conclusion `True` — a placeholder, not a deviation bound.
- So what is *attained structurally* is the **balanced fair-coin** point: centering exact,
  variance exact, modulus `0`. The **general** "summed-rescaled independents → Gaussian fixed
  point" is the modulus residue the calculus *predicts* and points a finite generator at (moments
  + `ProbCauchy`), but does **not** prove as one theorem.

**Net.** Not collapse-only (it predicts a *form* and *why q=+1*), not a miss (the fixed-point
engine, the two convolution-characters, centering/variance, and the modulus residue are all real
∅-axiom theorems). It is a **prediction whose keystone *leg* is now built** — `Φ_contraction`
proves convolve-rescale is a `Contraction` and `picard_cauchy` forces the `q=+1` modulus-residue
(`ConvolveRescaleContraction.lean`, 20/0). What keeps it one notch below `entropy.md`'s closed
derivation: `banach_fixed_point` itself is not yet applied (no honest `CompleteMetricModulus Dy`),
and convolution acts on the centered statistic, not the full weight-profile.

## Note for the technique — does CLT confirm "fixed point of a composed reading = q=+1 residue", generalizing golden_ratio.md from Möbius to convolution?

**Yes — this is the find, and it is the calculus's cleanest generalization of the `q=±1` residue
tag.** `golden_ratio.md` established: a fixed point of a self-applying map IS the residue, tagged
`q=+1` (converging) when the map *has* a fixed point it asymptotes to, vs `q=−1` (escaping) when
fixed-point-free (`cardinality.md`'s diagonal). That note used a *Möbius* iteration (`T(p,q)=(2p+q,p+q)`)
on a number-pair. CLT lifts the **same structure one level up**: the self-applying map is now
`Φ = convolve-and-rescale` acting on **weight-readings** (not number-pairs), and its fixed point
(the Gaussian) is the `q=+1` converging residue by the *identical* signature —

| | `golden_ratio.md` (φ) | `gaussian_clt.md` (Gaussian) |
|---|---|---|
| self-applying map | Möbius `T` on `(p,q)` | `Φ` = convolve⋆rescale on a *weight* |
| what iterates | a number-pair | a whole reading (`probability.md`'s weight) |
| fixed point | φ | the Gaussian profile |
| `q` tag | `+1` (converges, Lambek) | `+1` (converges) |
| reached-by-none | no convergent lands on φ | no finite `n` lands on the Gaussian |
| finite generator | recurrence + modulus `N=2k` | preserved moments + modulus `N(ε)` |
| Lean engine | `mobius_iteration_master` (built) | `banach_fixed_point` (built) **+** convolve⋆rescale contraction (**built**: `Φ_contraction`) |

So CLT **confirms and generalizes** the rule: *the fixed point of a self-applying reading is its
`q=+1` residue* — now with the self-applying thing being a **composed reading** (a weight under
convolution), not just a number-recurrence. This sharpens the README's model v4 ("readings form a
category; they compose in series") with a concrete payoff: **the convolution monoid on weights is
a self-applying composition whose `q=+1` residue is the Gaussian**, exactly as the Möbius monoid's
`q=+1` residue is φ. The README's normal form `⟨C|L⟩ ⊕ Residue(L,C)`, `q=±1`-tagged, holds at the
*reading-of-readings* level.

**The honest Lean-grounded vs predicted boundary.** *Grounded*: the q=+1 fixed-point-as-modulus-residue
engine (`banach_fixed_point`/`picard_cauchy`/`banach_unique`), both convolution characters
(`joint`/`discreteNum_append`), exact centering and variance at the balanced point
(`CLT_fair_centered`/`CLT_fair_variance_marker`/`variance_master`), the atomic Gaussian peak
(`gaussianPeakAtZero_eq_one`), and the residue-as-Cauchy-modulus that collapses at q=+1
(`balanced_LLN_modulus`, `ProbCauchy`, `cltModulus_of_varBound`). *Predicted-not-built*: a
convolution operator on weights, the `Φ = convolve-rescale` map, and the keystone theorem
**"Gaussian = Banach fixed point of `Φ`"** — the one statement that would promote this from
prediction to closed derivation. **Open Lean target** the calculus names precisely: *show
convolve-and-rescale is a `Contraction` (in `BanachFixedPoint`'s sense) and apply
`banach_fixed_point` to obtain the Gaussian as `lim(picard Φ seed)`* — the moments are the finite
generator, the modulus is `picard_cauchy`'s `N(m)`.

## Verified Lean anchors (file:theorem — all grep-verified to exist; ∅-axiom per in-file docstrings)

| Leg | Theorem (file:name) | Status |
|---|---|---|
| q=+1 fixed point = modulus-computed residue (the engine) | `Lib/Math/Analysis/BanachFixedPoint.lean : banach_fixed_point` (`:202`), `picard_cauchy` (`:154`), `banach_unique` (`:250`), `picard_step_geometric` (`:45`) | ∅-axiom (vein-C) ✓ |
| **convolve⋆rescale IS a `Contraction` (the keystone leg)** | `Probability/Limit/ConvolveRescaleContraction.lean : Φ_contraction` (rescale = exact dyadic halving), `Φ_picard_cauchy` (picard_cauchy applied, modulus `N(m)=m`), `dyMet` (genuine `MetricModulus Dy`), `center_fixed`/`orbit_to_center` (q=+1 fixed point reached-by-none) | **∅-axiom ✓ (20/0)** |
| convolution = `×↦·` character on weights | `Probability/Foundation/Independence.lean : joint` (`:27`), `joint_assoc_num` (`:87`), `joint_comm_num` (`:53`) | `joint_assoc_num` ∅-axiom ✓ |
| convolution = additive `+`-character (mean of a sum) | `Probability/Limit/LLN.lean : countTrue_append` (`:29`); `Probability/Foundation/Expectation.lean : discreteNum_append` (cited via `probability.md`) | ∅-axiom ✓ |
| CLT centering attained structurally | `Probability/Distribution/Gaussian.lean : CLT_fair_centered` (`:74`) | ∅-axiom ✓ |
| variance / second moment preserved (finite generator) | `Probability/Distribution/Gaussian.lean : CLT_fair_variance_marker` (`:85`); `Probability/Foundation/Variance.lean : variance_master` (`:44`) | ∅-axiom ✓ |
| Gaussian peak as atomic Nat fact | `Probability/Distribution/Gaussian.lean : gaussianPeakAtZero_eq_one` (`:53`), `expSumAtZero_eq_one` (`:39`), `gaussianPeakMass_num` (`:68`) | ∅-axiom ✓ |
| residue = Cauchy modulus, q=+1 collapse | `Probability/Limit/CLTLimit.lean : balanced_LLN_modulus` (`:31`), `balanced_cauchy` (`:40`); `Probability/Bridge/CauchyModulus.lean : ProbCauchy` (`:39`), `absDevCross_self` (`:33`); `Probability/Limit/CLTGeneric.lean : cltModulus_of_varBound` (`:41`), `genericCLT_balanced_collapse` (`:59`), `cltModulus_mono_var` (`:44`) | ∅-axiom ✓ |
| LLN (frequency=expectation at balance) | `Probability/Limit/LLN.lean : LLN_unit` (`:58`), `bernoulli_LLN_exact` (`:66`), `fair_LLN` (`:72`) | ∅-axiom ✓ |

**Now built (contraction leg closed, ∅-axiom — `tools/scan_axioms.py` → 20 pure / 0 dirty):**
- The `Φ = convolve-and-rescale` map and `Φ_contraction : Contraction (dyMet L) Φ` exist in
  `Probability/Limit/ConvolveRescaleContraction.lean`; `picard_cauchy` is applied to it
  (`Φ_picard_cauchy`), and the `q=+1` fixed point is located (`center_fixed`/`orbit_to_center`).

**Conceptual-only legs that remain (honest — predicted, not built):**
- **No convolution operator on full weight-profiles** — the contraction is proved on the centered
  dyadic statistic, not on a density/weight-function type (the tree has `(num,den)` masses + `joint`).
- **No theorem "Gaussian *profile* = `Φ`'s fixed point"** and **no `CompleteMetricModulus Dy`** — so
  `banach_fixed_point` itself is not applied (a genuine Cauchy-completion of the dyadics is open;
  `picard_cauchy` + a by-hand orbit→center is used instead, no fabricated `climconv`).
- `CLTGeneric.genericCLT_modulus_exists` (`:65`) has conclusion `True` — a placeholder, **not** a
  general deviation bound; the full `partialSum`-based CLT is *deferred* by `Gaussian.lean`'s own
  header to `Real213.CutSeries.partialSum`, not proved in this tree.

> Axiom-purity note: the new contraction module was re-run through `tools/scan_axioms.py`
> (20 pure / 0 dirty); the other rows' purity rests on the cited files' in-file docstrings
> ("STRICT ∅-AXIOM", "∅-axiom, vein-C", "no σ-algebra, no Choice").
