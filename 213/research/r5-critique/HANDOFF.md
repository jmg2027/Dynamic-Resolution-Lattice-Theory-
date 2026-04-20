# r5-critique — HANDOFF

## Status

**Phase E1–E3 Lean-complete (pending Raw build).**

Hypothesis H is Lean-confirmed at the counterexample level:
R1–R4 alone do not force ℂ.  Two concrete witnesses
(`ℤ[i]`, `ℤ[√-2]`) are fully verified modulo
`Raw.fold_swap_hom`, which is currently compiling in the slow
Lean 4 environment.

**Branch:** `claude/polish-paper-submission-EilC5`.

## What is in place

### Research notes
- `CLAUDE.md` — research frame, hypothesis H, E1–E5 list.
- `notes/00_research_question.md` — formalised question.
- `notes/01_zi_counterexample.md` — E1 writeup (ZI).
- `notes/02_r5_vacuity.md` — **E3**: R5 splits into R5a
  (Distinguishing) and R5b (completeness); R5b is the
  classical-infinity smuggling channel.

### Lean artifacts

**E1 (ZI = ℤ[i]):**
- `Research/ZI.lean` — structure, `mul`, `conj`, `normSq`.
- `Research/ZIDomain.lean` — `normSq_mul` (Diophantus via
  simp+omega), `no_zero_div`, `mul_ne_zero_of_ne_zero`.
- `Research/ZIHom.lean` — `conj_I`, `conj_negI`, `conj_mul`.
- `Research/ZILens.lean` — `ziLens_nonVanishing` (R3),
  `ziLens_swapMatching` (R4, uses `Raw.fold_swap_hom`).

**E2 (Z2 = ℤ[√-2], second witness):**
- `Research/ZSqrt2.lean`, `ZSqrt2Domain.lean`,
  `ZSqrt2Lens.lean`.
- Same structure as ZI with `a² + 2b²` norm; fully verified.

**E3 (R5 vacuity):**
- `Research/R5Vacuity.lean` — `foldTotality`,
  `foldTotality_vacuous`.

**Firmware support:**
- `Firmware/Raw.fold_swap_hom` added; `ring` → `Int.neg_add`
  patched.  Pending main build verification.

## Immediate next step

1. Wait for `lake build E213.Firmware.Raw` to finish.
2. Once Raw builds, verify all Lens modules (ziLens*,
   z2Lens*, R5Vacuity) build.
3. Generate final HANDOFF + commit.

## Not yet attempted

- **ZOmega (ℤ[ω] Eisenstein integers)** — structure + basic
  algebra was sketched but `normSq_nonneg` tripped up on
  omega's atom unification for the `-ab` term in the
  Eisenstein norm.  ZI and Z2 provide sufficient evidence.

## E4 — finding what re-selects ℂ

Given two explicit R1–R4 counterexamples (ZI, Z2) and the
vacuity of R5 within inductive Raw, the question becomes: is
there any 213-internal condition that would restore ℂ
uniqueness?  Candidates to explore:

- cardinality constraints (imports classical)
- Archimedean order (imports classical)
- closure under a Raw-internal notion of limit / growth
- categorical universal property
- physical/geometric relevance (ties to main research
  program rather than Paper 1 logic)

## Paper 2 stub

Working title: *"The ℝ-algebra assumption in 213 — a finitist
critique."*

Structure:
1. Recap of Paper 1's R1–R5 and its ℂ uniqueness theorem.
2. Split of R5 into R5a + R5b (Lean-backed in R5Vacuity).
3. Explicit countable counterexamples (ZI, Z2).
4. Consequence: ℂ uniqueness requires R5b, which is
   classical-infinity smuggling.
5. Finitist reformulation: R1–R4 + R5a; ℂ one admissible
   Lens in a larger spectrum.
