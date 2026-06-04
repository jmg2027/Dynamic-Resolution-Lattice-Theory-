# Measure Theory 213 — Module Index

Blueprint: `blueprints/math/05_measure_213.md` (retired).

## Modules

| File | Topic | Status |
|---|---|---|
| `MeasurableSet.lean` | `DyadicMeasurableSet := List DyadicBracket`; union/cardinality | ∅-axiom |
| `DyadicMeasure.lean` | `measureNum`; empty / singleton / additivity | ∅-axiom |
| `LebesgueIntegral.lean` | `lebesgueStepNum`; constant integrand `c·μ(S)`; union linearity | ∅-axiom |
| `Lp.lean` | `lpNormPow p f S`; constant / squared-norm / p=1 cases | ∅-axiom |
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

## Honest scope

  * Generic Hölder (`(Σ a²)(Σ b²) ≥ (Σ ab)²`) deferred — the
    Cauchy-Schwarz proof requires `(a-b)²` in `Nat`-arithmetic
    with case-split on `a ≤ b ∨ b ≤ a`; manageable but cosmetic.
  * `lp_one_singleton` covers the per-bracket `p=1 ↔ Lebesgue`
    collapse without funext.  The full `∀ S` form needs funext
    (leaks `Quot.sound` here) — pointwise version preserved.
