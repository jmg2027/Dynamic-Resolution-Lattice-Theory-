# r5-critique — HANDOFF

## Status

**Phase:** E1 — math argument complete, Lean partially
formalised. Hypothesis H **confirmed at the mathematical
level**; full Lean verification is the next iteration.

**Branch:** `claude/polish-paper-submission-EilC5` (shared with
Paper 1 polish; can be split later if needed).

## What is in place

- `CLAUDE.md` — research frame, hypothesis H, experiment list
- `notes/00_research_question.md` — formalised question
- `notes/01_zi_counterexample.md` — **full math argument**,
  R1–R4 verified by hand for `ziLens = (ZI, I, -I, ZI.mul)`.
  Conclusion: H confirmed mathematically.
- `framework/E213/Research/ZI.lean` — Gaussian integers with
  `mul`, `conj`, `normSq`; lemmas `ext`, `conj_conj`,
  `conj_ne_id`. **Builds ✓**.
- `framework/E213/Research/ZIDomain.lean` — `ZI.mul_comm`
  (manual, no `ring`). **Builds ✓**.
- `framework/E213/Research/ZILens.lean` — `ziLens` definition
  + base-value smoke tests. R3/R4 are documented as pending
  Lean formalisation (see file header).

## Immediate next step

Complete Lean R3 and R4:

1. **R3 (no zero divisors).** Needs `normSq_mul` (Diophantus
   identity, polynomial). Without `ring` in Lean 4 core,
   requires manual rewrites or adding a minimal polynomial
   helper. Write as `ZIDomain2.lean`.
2. **R4 (SwapMatching).** Needs Raw-level induction. Options:
   (a) add a general `Raw.fold_swap_hom` to
   `Firmware/Raw.lean`; (b) expose a public `Raw.rec`
   principle; (c) write E1-specific `Raw.fold_zi_swap` by
   Tree-level delegation (like existing `fold_signed_swap`).

The math argument in `notes/01_zi_counterexample.md` is
already sufficient to claim the counterexample at the level of
a research note.

## Open technical issues

- Lean 4 core has `Int` but not `Int`'s ring-theory lemmas
  bundled; may need to prove integral-domain property of `ZI`
  by hand (norm-based argument: `ZI.norm u v = |u|² · |v|²`).
- `Lens` structure currently lives in `E213.Hypervisor.Lens`;
  check whether `SwapMatching`, `NonVanishing` are general
  enough to apply to non-ℝ-algebra codomains (they should be —
  they take `α : Type` untyped).

## What comes after E1

- E2: generalise — classify all quadratic-extension Lenses
  satisfying R1–R4 (`ℚ[i]`, `ℚ(√-2)`, `𝔽_9`, etc.)
- E3: Lean formalisation of R5' (fold totality) and its vacuity
- E4: hunt for the minimal extra condition that restores
  ℂ-uniqueness — cardinality? archimedean? something else?

## Paper 2 stub (when E1+E2 are done)

Working title: "The ℝ-algebra assumption in 213 — a finitist
critique."

Outline draft planned in
`notes/99_paper2_outline.md` after E1–E3.
