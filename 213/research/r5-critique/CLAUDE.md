# r5-critique — Research Track

## Purpose

Test whether the paper's R5 constraint is actually doing the
logical work attributed to it, or whether it smuggles classical
infinity (Cauchy completeness, uncountable cardinality) to
justify the "α is an ℝ-algebra" assumption used in §4.

## Relationship to Paper 1 (`213/PAPER.md`)

- **This track does NOT modify Paper 1.** Paper 1 stays as a
  submission-ready, R5-using, mainstream-looking derivation.
- **Results here feed Paper 2** (planned: "The ℝ-algebra
  Assumption in 213: A Finitist Critique") and the `book/`
  program.

## Central hypothesis H

1. R5 is the bridge that makes "α is an ℝ-algebra" tenable in
   §4.1. Without R5, R1–R4 do **not** uniquely pick ℂ.
2. Concrete witnesses: countable quadratic Galois extensions
   such as `ℤ[i]`, `ℚ[i]`, `ℚ(√-2)` satisfy R1–R4.
3. Therefore the paper's "ℂ uniqueness" is valid only in a
   classical-infinity frame; under a finitist R5' (fold
   totality), the uniqueness collapses.

## Experiments

- **E1 (critical):** construct a Lens with codomain `ℤ[i]` and
  verify R1–R4 in Lean. **Expected: all four pass.**
- **E2:** weaken R4 from "ℝ-algebra aut" to "algebra aut over
  fixed field"; classify the admissible codomains.
- **E3:** formalise R5' (fold totality) in Lean; prove it is
  automatic for inductive Raw and adds no constraint.
- **E4:** identify minimal extra condition that re-selects ℂ
  among R1–R4-admissible codomains.
- **E5:** look for 213-internal reason (if any) that
  distinguishes ℂ beyond cardinality/completeness.

## Success / failure criteria

- **H confirmed** if E1 produces a working `ℤ[i]`-Lens with
  R1–R4 all satisfied, and no Raw-internal extra condition in
  E4/E5 closes the gap. → Paper 2 writable.
- **H refuted** if E1 fails at some Rk, or if E4/E5 surface a
  Raw-internal criterion that genuinely forces ℂ. → strengthens
  Paper 1, collapses Paper 2.

Either outcome is valuable.

## Directory layout

```
213/research/r5-critique/
  CLAUDE.md                       (this file)
  HANDOFF.md                      (state, next step)
  notes/
    00_research_question.md
    01_zi_counterexample.md       (E1 writeup)
    ...
```

Lean experiments live under
`213/framework/E213/Research/`.

## Style

- No Mathlib; Lean 4 core only (matches E213 policy).
- Every claim is either `theorem` in Lean or marked `[prose]`.
- Record negative results too.
