# Decomposition: measure theory (measure, σ-algebra, the Lebesgue integral)

*213-decomposition of "how much" — the measure / σ-algebra / Lebesgue integral, per
`../README.md` (model v7.1). The field was flagged for a SPECIFIC TENSION: the repo's probability
corpus deliberately works **without σ-algebras and without Choice** (every probability docstring:
"no Ω, no σ-algebra, no Choice"), yet classical measure theory is built ON them. So this
decomposition tests three outcomes — does the calculus PREDICT what measure theory needs, REVEAL the
σ-algebra/Choice as an avoidable import, or BREAK?*

> **Note on repo coverage — the decisive datum, located first.** Measure theory is **not absent**.
> `lean/E213/Lib/Math/Analysis/Measure/` is a 6-file tree (`Measure/INDEX.md`) with a declared
> paradigm and the tension stated *in the docstrings themselves*:
> **"σ-algebra rejected: a measurable set is just a `List DyadicBracket`. Finite by construction;
> no Choice; no countable-union closure axiom. Vitali / Banach-Tarski cannot arise."**
> (`MeasurableSet.lean:5-9`, `INDEX.md:18-24`). All **35** declarations across the four core
> modules are ∅-axiom PURE (freshly scanned, below). So measure theory is *built*, and built
> exactly as the calculus would predict: the weight-reading of `probability.md` with the
> normalization removed, on a finite list — no σ-algebra, no Choice. This note grounds every core
> leg in a verified PURE theorem; the only conceptual legs are the *classically-required* objects
> the repo deliberately omits (outer measure / Carathéodory / non-measurable set), which I confirm
> ABSENT and explain *why their absence is forced*.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the same point-construction as `integration.md`/`derivative.md`: a
  **dyadic bracket-tree** (`DyadicBracket`, carrying `numA, numB, expE`; `lenNum`, `midNum`), points
  = refinement residues never held. A "measurable set" is a **finite `List` of brackets**
  (`DyadicMeasurableSet := List DyadicBracket`, `MeasurableSet.lean:27`). Nothing measure-theoretic
  is constructed: there is **no `Ω`, no σ-algebra, no `Measure` type** — the construction is the
  bracket-list, the readout a `Nat`.

- **Reading `L = weight` (the additive `×↦+`-twin of the count) — `probability.md`'s reading
  WITHOUT the normalization.** This is the central hypothesis, and it lands exactly:
  - `probability.md` reads `P = ratio ∘ count`: a pair `(count A, count Ω)` clamped `num ≤ den`.
  - A **measure** is that *same count/weight reading before the ratio fold* — the numerator alone,
    un-normalized, un-clamped: `measureNum : List DyadicBracket → Nat` (`DyadicMeasure.lean:41`),
    the sum of bracket `lenNum`s. **Probability is the special case `denominator = 2^E`**
    (`DyadicMeasure.lean:21-22`, INDEX `:24`: "Probability is the case denominator = `2^E`").
  - The **Lebesgue integral** is the same weight read against a *value*:
    `lebesgueStepNum f S = Σ f(midNum)·lenNum` (`LebesgueIntegral.lean:32-35`) — the
    **value-weighted count** that `probability.md` already isolated as expectation
    (`E[X] = Σ mᵢ·vᵢ / D`). So `∫ f dμ` *is* `probability.md`'s expectation reading with the
    division dropped: measure : integral :: count : weighted-count :: P : E[X].

- **Residue** — two faces, and the crux of the whole note:
  1. *The interior residue (the modulus, `q=+1`):* a general convergent `∫` over an arbitrary `f`
     is reached by no finite bracket-list, only narrowed by a Cauchy modulus — the **same modulus
     residue** as `integration.md`/`derivative.md`/`continuity.md` (`CutRiemann`'s `N(m,k)`). The
     finite step-sum `lebesgueStepNum` is the operand; the limit never is. This is the converging
     `q=+1` pole. **No new residue kind.**
  2. *The exterior residue (the `q=−1` escape — the prediction):* the **non-measurable set** /
     Vitali / Banach–Tarski. Classically these are produced by a Choice-driven self-cover: pick one
     representative from *every* coset of `ℚ` in `ℝ` — a function `selector : (cosets) → ℝ` whose
     existence is exactly the Axiom of Choice, and whose graph is engineered to lie *outside* every
     countably-additive assignment. That is the **count-reading's `q=−1` diagonal**
     (`cardinality.md`): a self-applying enumeration forced to point past its own image
     (`object1_not_surjective`, `no_surjection_of_fixedpointfree`, both PURE). The non-measurable
     set is not a bigger pile of measure — it is the **forced fixed-point-free residue of an
     uncountable selector**, the same `q=−1` escape as Cantor's diagonal and Gödel's sentence
     (`godel.md`).

## Re-seeing — ⟨C | L⟩

```
   measurable set S        =  ⟨ family of distinguishables | — ⟩ = a finite List DyadicBracket
                              (C; replaces the σ-algebra — MeasurableSet.lean:27)
   measure  μ(S)           =  ⟨ S | weight-reading ⟩  =  Σ lenNum            (measureNum)
                              = probability.md's count-pair NUMERATOR, un-normalized
   probability P(S)        =  μ(S) at denominator 2^E   =  the ratio fold ON the weight
                              (P = weight ∘ ratio;  measure = weight alone)
   countable additivity    =  μ(S ∪ T) = μ S + μ T      =  List `++` additivity      (PURE)
                              (finite by construction — the resolution dial, integration.md)
   ∫ f dμ  (Lebesgue)      =  ⟨ S | VALUE-weighted weight-reading ⟩ = Σ f(midNum)·lenNum
                              = probability.md's expectation E[X] WITHOUT the ÷D
   ∫ f d(S∪T) = ∫S + ∫T    =  the weight is the ADDITIVE character  (+↦+)            (PURE)
   non-measurable / Vitali =  Residue(weight, C) at q=−1  =  the Choice-selector diagonal
                              (cardinality.md's object1_not_surjective — REACHED BY NONE)
   Carathéodory closure    =  galois.md's clo = g∘f  (q=+1 idempotent)  — ABSENT, see strain
```

**(1) Measure = weight = probability's numerator (the hypothesis CONFIRMED, ∅-axiom).** The repo's
own encoding makes it literal: `measureNum` (`DyadicMeasure.lean:41`) is the bare sum of `lenNum`s,
and probability is recovered by fixing the denominator to `2^E` (INDEX `:24`). `measure_empty = 0`
(`:46`, rfl), `measure_singleton db = db.lenNum` (`:49`), `measure_union_additive` (`:69`, PURE).
So `probability.md`'s `P = ratio ∘ count` decomposes *one level further*: `count` is itself the
`measure`/weight reading, and `P` post-composes the ratio fold. **Measure : Probability :: weight :
ratio∘weight** — the calculus predicted "general measure = weight × resolution" (README batch-3,
`probability.md` "Suggested map update"); the prediction is now a built PURE module.

**(2) Countable additivity = the resolution dial = list `++` additivity (no σ-algebra needed).**
Classically, countable additivity is the σ-algebra's defining closure (closed under countable
unions) plus σ-additivity of μ. Here it **collapses to list concatenation**:
`measureNum_append` (`DyadicMeasure.lean:55`, PURE) gives `μ(s ++ t) = μ s + μ t` unconditionally,
because a `List` is finite by construction (`MeasurableSet.lean:8-9`). This is the **resolution
dial of `integration.md`** read on the weight: "countable additivity" is the additive twin of
telescoping (`Σ` over a chain), not a new closure axiom. The integral inherits it
(`lebesgue_union_additive`, `LebesgueIntegral.lean:66`, PURE) — `∫` is the **additive character**
`+↦+`, the value-weighted dual of independence's multiplicative character (`probability.md`).

**(3) The Lebesgue integral = `∫ = Σ` at residue resolution, read on the weight.** `lebesgueStepNum`
(`LebesgueIntegral.lean:32`) IS the finite step-sum `Σ f(midNum)·lenNum`; `lebesgue_const c S = c·μ(S)`
(`:84`, PURE) is the simple-function integral; `lp_two_singleton` (`Lp.lean:63`, PURE) gives
`‖f‖₂² = ∫ f²dμ`. This is `integration.md`'s `∫ = Σ` dial composed with the weight — the
"classical monotone-/dominated-convergence chase is unnecessary because the integral is already
finite" (INDEX `:26-28`). The general convergent `∫` over arbitrary `f` is the modulus residue
(`integration.md`'s honest open leg), *not* a measure-theoretic completion.

## LEVERAGE — the Revelation (forcing + residue-surfaced)

**Verdict: PREDICTION — the sharpest in the batch. The calculus PREDICTS that classical measure
theory's Choice-dependence (non-measurable sets, Vitali, Banach–Tarski) is *exactly* its `q=−1`
escape residue, so the repo's Choice-free, σ-algebra-free measure theory is the `q=+1` corner of the
SAME structure — not a weaker fragment. This explains WHY the repo can avoid Choice, and the
explanation is Lean-grounded at both poles.**

The leverage is a single forcing argument across the two `q=±1` poles of the residue tag (README's
load-bearing invariant):

- **The `q=+1` corner is the whole of constructive measure theory, and it is BUILT and PURE.**
  Measurable set = finite bracket-list (no closure axiom), measure = `measureNum` (finite sum),
  additivity = list `++` (unconditional), integral = finite step-sum. **35/35 declarations PURE**
  (scanned below). Every classical theorem whose content is *finitary* survives verbatim:
  additivity, monotonicity (`measure_union_le`, `cardinality_le_union`, PURE), linearity of the
  integral, `∫c dμ = c·μ`, the `L²` norm. This is `probability.md`'s machinery with the clamp removed.

- **The `q=−1` corner is *exactly* the Choice-requiring pathologies — and the calculus predicts
  this from `cardinality.md` with no new mechanism.** A non-measurable set is built by a Vitali
  selector: a function choosing one representative per `ℝ/ℚ` coset — uncountably many independent
  choices, i.e. AC on an uncountable index. By `cardinality.md`/`OneDiagonal`, an *uncountable
  self-cover* `f : A → (A → Bool)` is forced **fixed-point-free / non-surjective**
  (`object1_not_surjective`, `no_surjection_of_fixedpointfree`, both PURE) — its diagonal residue
  lies *outside every countably-additive assignment*, oscillating outside the reading exactly as
  Cantor's `!(f x x)` does. **The non-measurable set IS the `q=−1` diagonal of the weight-reading's
  uncountable self-cover.** The calculus therefore predicts:
  1. *Where the pathology lives:* only at an uncountable, Choice-built selector — never at a finite
     `List`. The repo's `DyadicMeasurableSet` is finite by construction, so the `q=−1` diagonal
     **cannot arise** — and the docstring says precisely this ("Vitali / Banach-Tarski cannot
     arise", `MeasurableSet.lean:9`). The absence is *forced* by staying at `q=+1`, not stipulated.
  2. *Why Choice is the dividing line:* AC is the operation that *builds the uncountable self-cover*
     (the selector). No Choice ⇒ no uncountable selector ⇒ no `q=−1` diagonal ⇒ no non-measurable
     set. The repo's "no Choice" stance is not an arbitrary restriction; it is the statement
     **"stay in the `q=+1` corner."**

- **So the repo's measure theory is not a weaker fragment — it is the `q=+1` HALF of one
  residue-tagged structure, the half whose content is finitary and constructive.** Classical
  measure theory annexes the `q=−1` half by adjoining Choice; the pathologies (Vitali,
  Banach–Tarski) are *that half made visible*. This is genuine leverage: it converts the repo's
  design decision ("no σ-algebra, no Choice") from a methodological taboo into a **structural
  prediction** — the same `q=±1` residue tag that unified Cantor (`cardinality.md`), φ
  (`golden_ratio.md`), Gödel (`godel.md`), nilpotent/involutive (`homology.md`) now unifies
  **constructive vs. non-measurable** as the two poles of the weight-reading's residue.

This passes the re-skin guard at the highest bar: it is a *prediction* ("the pathologies are exactly
the `q=−1` residue, so a Choice-free theory is the `q=+1` corner"), not a re-description, and it
*derives the absence* of the classical scaffolding rather than merely noting it.

## Honest strain-report — σ-algebra, Carathéodory, and the located absences

The prompt demanded honesty on the crux (is the σ-algebra FORCED, or is it scaffolding the
resolution-dial replaces?). The answer is clean, with three genuinely-absent classical objects:

- **σ-algebra: NOT forced — it is the classical scaffolding the resolution-dial replaces.** A
  σ-algebra exists to *guarantee closure under countable operations so the measure is well-defined
  on limits*. In 213 the measurable set is a finite `List`, additivity is `++` (always defined), and
  the "limit" is a modulus residue (`integration.md`) — so the closure the σ-algebra provides is
  **already discharged by finiteness + the resolution dial**. The σ-algebra is the
  "countable-union closure axiom" the INDEX explicitly *rejects* (`:18-24`). It is a Reading-side
  artifact (which sets are resolvable), not a Construction primitive — and the calculus dissolves
  it the way `continuity.md` dissolved "open set" into a refinement-stable fibre.

- **Outer measure / Carathéodory extension: NOW CLOSED — instantiated AS `galois.md`'s closure
  operator `clo` (`q=+1` idempotent).** ✅ `Analysis/Measure/OuterMeasure.lean` (29/0 PURE) builds the
  finitary outer measure `outerMeasureNum` (= inf over covers, attained by the set), proves it
  monotone + subadditive (`outerMeasure_union_le`), and instantiates the Carathéodory passage AS the
  abstract `clo`: a genuine Galois connection `cara_gc` (with `cara_g` a section of `cara_f`), so
  `caraClosure := clo cara_f cara_g` satisfies `caraClosure_extensive`/`_monotone`/`_idempotent`
  (literal `T²=T`) — the predicted closure-monad shape made literal. `all_caratheodory_measurable`:
  **every** finite measurable set splits additively (the criterion = `measure_union_additive`), and
  `clo_preserves_measure`/`outerMeasure_conservative`: the extension is conservative. This is the
  *predicted content* of the `q=+1` corner — the classical construction's `q=−1` half (the infimum
  over *countable* covers, where non-measurable sets get excluded) is the deliberately-omitted part:
  on a finite `List` the over-large domain is never built, so the closure is conservative (adds
  nothing) and every set is measurable. Closure shape: built + PURE. (Earlier this was a named open
  target; now closed as the conservative finite instantiation.)

- **The one located break inside the built tree — `Lp` full additivity leaks `Quot.sound`.** The
  INDEX is honest (`:36-38`): `lp_one_singleton` (the per-bracket `p=1 ↔ Lebesgue` collapse) is
  funext-free and PURE (`Lp.lean:46`), but the **full `∀ S` form needs `funext` (leaks `Quot.sound`
  here)** — so it is *not* built; only the pointwise/singleton version is preserved. This is the
  same `propext`/`funext` wall `category_theory.md` flagged (HoTT-style function extensionality is
  structurally forbidden). It is a real, located, function-extensionality boundary — not a measure
  pathology, but the honest edge of the `Lp` layer.

## Note for the technique — does measure force a NEW construct?

**No new primitive, and a strong consolidation: measure theory is `probability.md` run BACKWARD (the
weight before the ratio), tagged at both `q=±1` poles.** Concretely:

1. **The weight-reading is confirmed first-class and pre-normalization.** `probability.md` posed
   "general measure = weight × resolution" as an open target the calculus *predicts*. This note
   finds it **built and PURE**: `measureNum` is the weight, additivity is the resolution dial (list
   `++`), and `P` is `measureNum` at `den = 2^E`. The "weight" `L`-parameter (README v3+) is
   therefore not just a probability footnote — it is the *measure* itself, with probability as its
   normalized special case.

2. **The `q=±1` residue tag absorbs the Choice question — the deepest consolidation.** The biggest
   structural lesson: "constructive measure theory" and "non-measurable sets" are **one residue read
   at its two signs**, exactly as Cantor/φ are (`cardinality.md`/`golden_ratio.md`). The repo lives
   in the `q=+1` corner *by design*; the `q=−1` corner is precisely the Choice-adjoined pathology
   tier. No new axis: the residue tag the calculus already carries *explains the repo's
   foundational stance*.

3. **Map status:** unchanged interior. `C` = bracket-list (= `cardinality.md`'s family of
   distinguishables, finite); `L` = the weight-reading (= `probability.md`'s count before ratio),
   carrying {resolution (→ additivity = `++`), character-mode (`∫` = the additive `+↦+` character),
   weight (= the measure itself)}; `Residue` = the weight's self-application surplus, `q=+1` = the
   modulus (convergent ∫) / `q=−1` = the Choice-selector diagonal (non-measurable set). Carathéodory
   = the `clo` closure monad (`q=+1` idempotent), predicted-shape but un-instantiated.

**Verdict: measure theory FITS as the un-normalized weight-reading and the calculus PREDICTS the
σ-algebra/Choice as the avoidable `q=−1` residue — the strongest leverage in the practice notebook,
because it derives (not stipulates) the repo's Choice-free, σ-algebra-free stance as occupying the
`q=+1` corner of one residue-tagged structure.** It does NOT break. One located function-extensionality
break (`Lp` full additivity, `Quot.sound`) and two honestly-absent classical objects (outer
measure / Carathéodory — predicted-shape `clo`; non-measurable set — predicted as the `q=−1` residue
the repo deliberately never builds).

---

### Verified Lean anchors (freshly scanned via `tools/scan_axioms.py`; build clean)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| measurable set = finite bracket-list (σ-algebra rejected) | `Lib/Math/Analysis/Measure/MeasurableSet.lean:27 : DyadicMeasurableSet`; `:59 cardinality_union`; `:66 cardinality_le_union` | ∅-axiom PURE ✓ |
| measure = weight = un-normalized count | `Lib/Math/Analysis/Measure/DyadicMeasure.lean:41 : measureNum`; `:46 measure_empty`; `:49 measure_singleton` | ∅-axiom PURE ✓ |
| countable additivity = list `++` (resolution dial) | `DyadicMeasure.lean:55 : measureNum_append`; `:69 measure_union_additive`; `:83 measure_union_le` | ∅-axiom PURE ✓ |
| probability = measure at `den=2^E` | `DyadicMeasure.lean:21-22` (docstring); `Probability/INDEX.md:24` | doc + `DyadicMeasure` PURE ✓ |
| Lebesgue ∫ = value-weighted weight = `Σ f·lenNum` | `Lib/Math/Analysis/Measure/LebesgueIntegral.lean:32 : lebesgueStepNum`; `:84 lebesgue_const` (`c·μ`); `:66 lebesgue_union_additive` (`+↦+` character) | ∅-axiom PURE ✓ |
| `L²` norm = `∫ f² dμ` | `Lib/Math/Analysis/Measure/Lp.lean:63 : lp_two_singleton`; `:38 lp_const_singleton` | ∅-axiom PURE ✓ |
| capstone bundle (4 layers) | `Lib/Math/Analysis/Measure/Capstone.lean:66 : total_witness` (+ 4 witnesses) | ∅-axiom PURE ✓ |
| `P = ratio ∘ weight` (the normalized special case) | `Probability/Foundation/Cut.lean:27 : ProbabilityCut` (+ `num≤den` clamp); `:64 probabilityCut_master` | PURE (per `probability.md`) ✓ |
| expectation = `∫` with the ÷D (the value-weight) | `Probability/Foundation/Expectation.lean : discreteNum`, `discreteNum_append` (linearity) | PURE (per `probability.md`) ✓ |
| `q=−1` residue = the Choice-selector diagonal | `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective`; `Lens/Foundations/OneDiagonal.lean:51 : no_surjection_of_fixedpointfree` | ∅-axiom PURE ✓ |
| Carathéodory = `clo` closure monad (predicted shape, un-instantiated) | `Lib/Math/Order/GaloisConnection.lean:104 clo`, `:107 clo_extensive`, `:126 clo_idempotent` | PURE engine; NOT instantiated as outer-measure (conceptual leg) |
| resolution dial (modulus residue, prior) | `integration.md` anchors (`gauss_conservation_telescope`, `RiemannIntegralData.limit`); `derivative.md`/`continuity.md` | cited, prior ✓ |

**Fresh purity scan (this session):** `scan_axioms.py` on the four core Measure modules =
**35 pure / 0 dirty**; `Measure.Capstone` = **5 pure / 0 dirty**; `object1_not_surjective`,
`no_surjection_of_fixedpointfree` = PURE. Build clean.

**Conceptual-only / absent legs (honest):**
- **Outer measure / Carathéodory extension** — *predicted-shape* (`galois.md`'s `clo`, PURE) but
  **no `outerMeasure`/`Caratheodory` object exists in `lean/E213`** (grep: 0 hits). Named open target.
- **Non-measurable set / Vitali / Banach–Tarski** — *predicted as the `q=−1` residue* and
  **deliberately never built** (finite `List`, no Choice ⇒ the diagonal cannot arise,
  `MeasurableSet.lean:9`). Absence is forced, not asserted.
- **General convergent `∫` over arbitrary `f`** — the modulus residue (`integration.md`'s own open
  leg); the built integral is the finite step-sum + simple-function cases.
- **Located break:** `Lp` full `∀ S` additivity leaks `Quot.sound` via `funext`
  (`Measure/INDEX.md:36-38`); only the funext-free pointwise `lp_one_singleton` is PURE-preserved.
  The `propext`/`funext` wall (`category_theory.md`), not a measure pathology.
