# Measure Theory 213 — Module Index

Blueprint: `blueprints/math/05_measure_213.md` (retired).

## Modules

| File | Topic | Status |
|---|---|---|
| `MeasurableSet.lean` | `DyadicMeasurableSet := List DyadicBracket`; union/cardinality | ∅-axiom |
| `DyadicMeasure.lean` | `measureNum`; empty / singleton / additivity | ∅-axiom |
| `LebesgueIntegral.lean` | `lebesgueStepNum`; constant integrand `c·μ(S)`; union linearity | ∅-axiom |
| `Lp.lean` | `lpNormPow p f S`; constant / squared-norm / p=1 cases | ∅-axiom |
| `OuterMeasure.lean` | `outerMeasureNum` (μ\*); Carathéodory passage = `clo` closure (extensive/monotone/idempotent); conservativity | ∅-axiom |
| `Capstone.lean` | 5 cluster witnesses + `total_witness` | ∅-axiom |
| `Measure.lean` | umbrella | — |

## 213-native paradigm

  * **σ-algebra rejected**: a measurable set is just a `List
    DyadicBracket`.  Finite by construction; no Choice; no
    countable-union closure axiom.  Vitali / Banach-Tarski
    cannot arise.
  * **Measure = finite Nat sum**: `measureNum` adds bracket
    `lenNum`s.  "Countable additivity" reduces to list `++`
    additivity (term-mode induction).
  * **Lebesgue integral = step-function sum**: `lebesgueStepNum f
    S = Σ f(midNum) · lenNum`.  The classical
    monotone-/dominated-convergence chase is unnecessary because
    the integral is already finite.
  * **Lp = pointwise pow + integral**: no completeness chase.
  * **Carathéodory = `clo` closure (instantiated)**: `outerMeasureNum`
    (μ\*) is the infimum-over-covers attained by the set itself
    (`outerMeasure_is_inf_cover`), monotone + subadditive
    (`outerMeasure_union_le`).  The outer-measure→measurable passage is
    a genuine Galois connection (`cara_f = measureNum ⊣ cara_g =`
    canonical single-bracket) whose induced `clo`
    (`Order/GaloisConnection.lean`) is the Carathéodory-measurable
    representative: **extensive** (`caraClosure_extensive`), **monotone**
    (`caraClosure_monotone`), **idempotent** (`caraClosure_idempotent`,
    literal `T²=T` since `cara_fg : f∘g = id`).  The extension is
    **conservative** (`outerMeasure_conservative` rfl;
    `clo_preserves_measure`), and **every** finite measurable set is
    Carathéodory-measurable (`all_caratheodory_measurable` =
    `measure_union_additive` read as the splitting criterion — the
    `q=−1` non-measurable residue cannot arise on a finite `List`).
    This closes measure.md's named open target.

## Honest scope

  * Generic Hölder (`(Σ a²)(Σ b²) ≥ (Σ ab)²`) deferred — the
    Cauchy-Schwarz proof requires `(a-b)²` in `Nat`-arithmetic
    with case-split on `a ≤ b ∨ b ≤ a`; manageable but cosmetic.
  * `lp_one_singleton` covers the per-bracket `p=1 ↔ Lebesgue`
    collapse without funext.  The full `∀ S` form needs funext
    (leaks `Quot.sound` here) — pointwise version preserved.
